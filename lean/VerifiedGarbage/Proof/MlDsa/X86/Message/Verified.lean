module

import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
meta import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Impl.MlKem.X86.Basic
meta import VerifiedGarbage.Impl.MlKem.X86.Basic
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Entry
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlKem.X86.TopKem
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
meta import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Entry
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.MlDsa.X86.Verify.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params

/-! ### `MlDsa.X86.Verify.Entry`, which only this module used -/

section

/-!
# ML-DSA verification on x86 (32-bit): the entries

`vg_mldsa*_verify` and `vg_mldsa*_verify_prepared`
(`Impl/MlDsa/X86/Verify/Entry.lean`) call the core (`verifyCoreContract`)
with `t̂₁` in the buffer `t` (`core_piece`): the first computes it in its
`scratch` (`t1s_piece`), the second finds it in its prepared key. They are
proven as the other top-level functions on x86, in a layout of their own
(`YVE`: the key, of `kl` bytes, `mu`, `sig`, `scratch` and 136 bytes of
stack), with runs related by the pointers and their inputs, which
verification may leak (`lkV`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.VerifyEntry

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (setArgs callP callPR seqR)
open VG.Proof.MlDsa.X86.Verify (verifyCoreContract verifyCoreSig T1In vPk vMu vSig lkV VFacts vfacts PrimsOk)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlDsa.Verify (t1Hat vT1)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece with a precondition `φ` on the initial state, which it keeps. -/
theorem piece_pureV {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop} {c : Prog isa}
    (φ : State → Prop) (h : Piece Pre Pub A B c) :
    Piece Pre Pub (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

/-- The entries' layout, for a key of `kl` bytes. -/
def YVE (p : Params) (kl : Nat) : Lay :=
  ⟨[(kl, false), (64, false), (p.sigLen, false), (scratchWords p * 8, true)], 3, 136⟩

/-- The pieces of the entries. -/
abbrev VE (p : Params) (kl : Nat) := Piece (TPre (YVE p kl)) (TPub (YVE p kl) (lkV p))

/-- The result of verification of the inputs on entry, in `eax`. -/
def VDone (p : Params) (s₀ s : State) : Prop :=
  let v := fun b => verifyMu p b (vPk p s₀) (vMu s₀) (vSig p s₀)
  (s.gpr .eax = 1 ∧ ∃ b, v b = some true) ∨ (s.gpr .eax = 0 ∧ v minBounds ≠ some true)

section
variable {p : Params} {kl : Nat} {A : State → State → Prop}

theorem yve_n (p : Params) (kl : Nat) : (YVE p kl).n = 4 := rfl

theorem okA {i o l : Nat} (hi : i < 4) (hl : 0 < l) (h : o + l ≤ (YVE p kl).alen i) :
    (YVE p kl).ok ⟨i, o, l⟩ = true := Lay.ok_iff.mpr ⟨hi, hl, h⟩

theorem okWS {o l : Nat} (hl : 0 < l) (h : o + l ≤ scratchWords p * 8) :
    (YVE p kl).okW ⟨3, o, l⟩ = true := Lay.okW_iff.mpr ⟨okA (by decide) hl h, rfl⟩

/-- Bytes of a region at `x + o`, from those of a region at `x` around it. -/
theorem off_congr {m m' : Mem} {x : Addr} {L : Nat} (h : ∀ j < L, m' (x + BitVec.ofNat 64 j) = m (x + BitVec.ofNat 64 j))
    {o len : Nat} (ho : o + len ≤ L) : ∀ i < len, m' (x + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
      m (x + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := fun i hi => by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega_using [ho, hi])

/-- The call of the core, with `t̂₁` in the buffer `t`. -/
theorem core_piece {n : String} {f : Prog isa} (hv : Verified X86.target f (verifyCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (hF : VFacts p) (hkl : p.pkLen ≤ kl) (t : Buf)
    (htl : t.len = 1024 * p.k) (ht : (YVE p kl).ok t = true)
    (hts : (YVE p kl).sep t ⟨3, 0, oT1 p⟩ = true) {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p t)))
      ht').isSome = true)
    (hA : ∀ s₀ s, TPre (YVE p kl) s₀ → A s₀ s → Ctx (YVE p kl) s₀ s ∧
      ∀ r < p.k, PolyIs s.mem (Buf.addr s₀ t + BitVec.ofNat 64 (1024 * r)) (t1Hat (vPk p s₀) r)) :
    VE p kl A (fun s₀ s' => Ctx (YVE p kl) s₀ s' ∧ VDone p s₀ s') (callPR 3 n f (coreArgs p t)) := by
  have hk := hF.k
  have hpk := hF.pk
  have hsig := hF.sig
  have hscr := hF.scr
  have hsw := hF.sw
  obtain o0 : (YVE p kl).ok ⟨0, 0, p.pkLen⟩ = true := okA (by decide) (by omega_using [hpk]) (by simp [YVE, Lay.alen]; omega_using [hkl])
  obtain o1 : (YVE p kl).ok ⟨1, 0, 64⟩ = true := okA (by decide) (by decide) (by simp [YVE, Lay.alen])
  obtain o2 : (YVE p kl).ok ⟨2, 0, p.sigLen⟩ = true := okA (by decide) (by have := hF.ct; omega_using [hk, hsig]) (by simp [YVE, Lay.alen])
  obtain w3 : (YVE p kl).okW ⟨3, 0, oT1 p⟩ = true := okWS (by simp only [oT1]; omega_using [hscr]) (by simp only [oT1]; omega_using [])
  obtain r3 := (Lay.okW_iff.mp w3).1
  refine callPR_pieceK (lk := lkV p) (K := 96) (coreArgs p t) [⟨0, 0, p.pkLen⟩, ⟨1, 0, 64⟩, ⟨2, 0, p.sigLen⟩, t]
    [⟨3, 0, oT1 p⟩] (fun _ _ h => h) hv hsp hst (by simp [coreArgs])
    (by simp [coreArgs]) (by simp [coreArgs, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, o0, o1, o2, r3, ht])
    (by simp [YVE]) (by simp [YVE]) (by simp [o0, o1, o2, ht]) (by simp [w3]) tt
    (fun s₀ s hp h => (hA s₀ s hp h).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨hc, ht1⟩ := hA s₀ s hp ha
    obtain hpkb : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    obtain hkp : T1In p e.mem (Buf.addr s₀ t) (bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen) := by
      intro r hr
      rw [hpkb, PreparedKey.public_poly p _ hr]
      exact Proof.MlDsa.Verify.polyIs_congr (off_congr (he.mem _ ht) (by rw [htl]; omega_using [hr])) (ht1 r hr)
    obtain ⟨b₀, b₀', b₀'', b₀f⟩ := he.bufK hp (by simp [coreArgs]) o0 (K := 96) (by simp [YVE])
    obtain ⟨b₁, b₁', b₁'', b₁f⟩ := he.bufK hp (by simp [coreArgs]) o1 (K := 96) (by simp [YVE])
    obtain ⟨b₂, b₂', b₂'', b₂f⟩ := he.bufK hp (by simp [coreArgs]) o2 (K := 96) (by simp [YVE])
    obtain ⟨b₃, b₃', b₃'', b₃f⟩ := he.bufK hp (by simp [coreArgs]) r3 (K := 96) (by simp [YVE])
    obtain ⟨b₄, b₄', b₄'', b₄f⟩ := he.bufK hp (by simp [coreArgs]) ht (K := 96) (by simp [YVE])
    obtain ⟨x₁, x₂⟩ := he.selfK hp (by simp [coreArgs]) (K := 96) (by simp [YVE])
    obtain ⟨en, hE⟩ := he.espNat hp (by simp [YVE]) (by simp [coreArgs])
    obtain hE2 : 120 ≤ (E1 s₀).toNat := by
      rw [E1_nat s₀ hp.E0_big]; have := hp.sp; simp only [YVE] at this; omega_using [this]
    obtain d03 := Buf.disj hp o0 r3 (by simp [Lay.sep, YVE, Lay.awr])
    obtain d13 := Buf.disj hp o1 r3 (by simp [Lay.sep, YVE, Lay.awr])
    obtain d23 := Buf.disj hp o2 r3 (by simp [Lay.sep, YVE, Lay.awr])
    obtain dt3 := Buf.disj hp ht r3 hts
    have dt3' := dt3.symm
    have := (E1 s₀).isLt
    obtain a₀ := he.arg 0 (by simp [coreArgs])
    obtain a₁ := he.arg 1 (by simp [coreArgs])
    obtain a₂ := he.arg 2 (by simp [coreArgs])
    obtain a₃ := he.arg 3 (by simp [coreArgs])
    obtain a₄ := he.arg 4 (by simp [coreArgs])
    have aa := he.argAddr0
    obtain e3 : (scratchWords p - 128 * p.k) * 8 = oT1 p := by simp only [oT1]; omega_using []
    generalize e = e' at *
    sig_pre [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, coreArgs, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Impl.MlDsa.X86.KeyGen.Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul, Buf.addr, Buf.rgn, wrR, below, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, e3, htl] at *
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega_arith
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [coreArgs, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, o0, o1, o2, r3, ht]) he he'
    obtain ⟨hc, -⟩ := hA s₀ s hp ha
    obtain ⟨hc', -⟩ := hA s₀' s' hp' ha'
    obtain l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    obtain l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = vMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    obtain l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    obtain l₁' : bytesAt e'.mem (Buf.addr s₀' ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o0)]; exact hc'.roBytes hp' o0 rfl
    obtain l₂' : bytesAt e'.mem (Buf.addr s₀' ⟨1, 0, 64⟩) 64 = vMu s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o1)]; exact hc'.roBytes hp' o1 rfl
    obtain l₃' : bytesAt e'.mem (Buf.addr s₀' ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o2)]; exact hc'.roBytes hp' o2 rfl
    have hl := hq.2.2
    simp only [lkV] at hl
    obtain a₀ := he.arg 0 (by simp [coreArgs])
    obtain a₁ := he.arg 1 (by simp [coreArgs])
    obtain a₂ := he.arg 2 (by simp [coreArgs])
    obtain a₀' := he'.arg 0 (by simp [coreArgs])
    obtain a₁' := he'.arg 1 (by simp [coreArgs])
    obtain a₂' := he'.arg 2 (by simp [coreArgs])
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a₀, a₁, a₂, a₀', a₁', a₂', coreArgs, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Impl.MlDsa.X86.KeyGen.Arg.val, Buf.addr] at *
    refine ⟨esp, ?_, hq.ptr o0, hq.ptr o1, hq.ptr o2, ags 3 (by simp), ags 4 (by simp)⟩
    simp only [l₁, l₂, l₃, l₁', l₂', l₃', hl]
  · obtain ⟨hc, -⟩ := hA s₀ s hp ha
    obtain l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    obtain l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = vMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    obtain l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    obtain a₀ := he.arg 0 (by simp [coreArgs])
    obtain a₁ := he.arg 1 (by simp [coreArgs])
    obtain a₂ := he.arg 2 (by simp [coreArgs])
    generalize e = e' at *
    sig_post [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, coreArgs, List.getElem_cons_zero, List.getElem_cons_succ,
      VG.Impl.MlDsa.X86.KeyGen.Arg.val, g₂, sw_app, Buf.addr] at post l₁ l₂ l₃
    refine ⟨h', ?_⟩
    unfold VDone
    rw [← l₁, ← l₂, ← l₃]
    exact post

/-! ## `vg_mldsa*_verify` -/

/-- `t̂₁` of the rows before `r`, in `scratch`. -/
def TI (p : Params) (r : Nat) (s₀ s : State) : Prop :=
  Ctx (YVE p p.pkLen) s₀ s ∧ ∀ j < r, PolyIs s.mem (Buf.addr s₀ (t1S p j)) (t1Hat (vPk p s₀) j)

theorem t1S_ok (hF : VFacts p) {j : Nat} (hj : j < p.k) : (YVE p p.pkLen).okW (t1S p j) = true := by
  obtain hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  exact okWS (by decide) (by simp only [oT1]; omega_using [hj, hsw])

theorem ws_ok (hF : VFacts p) : (YVE p p.pkLen).okW (sb 0 1024) = true := by
  obtain hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  exact okWS (by decide) (by omega_using [hsw])

/-- Row `r` of `t̂₁`. -/
theorem t1One_piece {P : Prims} (hP : PrimsOk P) (hF : VFacts p) {r : Nat} (hr : r < p.k) :
    VE p p.pkLen (TI p r) (TI p (r + 1)) (t1One p P r) := by
  obtain hk := hF.k; have hsw := hF.sw; have hscr := hF.scr; have hpk := hF.pk
  obtain ws := ws_ok hF
  obtain tr := t1S_ok hF hr
  obtain vo : (YVE p p.pkLen).ok ⟨0, 32 + 320 * r, 320⟩ = true :=
    okA (by decide) (by decide) (by simp only [YVE, Lay.alen, List.getD_cons_zero]; omega_using [hr, hpk])
  obtain vall : (YVE p p.pkLen).ok ⟨0, 0, p.pkLen⟩ = true :=
    okA (by decide) (by omega_using [hpk]) (by simp only [YVE, Lay.alen, List.getD_cons_zero]; omega_using [])
  obtain sepT : ∀ j < p.k, j ≠ r → (YVE p p.pkLen).sep (t1S p j) (t1S p r) = true := fun j hj hne =>
    VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, by simp only; omega_using [hne]⟩)
  obtain sepW : ∀ j < p.k, (YVE p p.pkLen).sep (t1S p j) (sb 0 1024) = true := fun j hj =>
    VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, .inr (by simp only [oT1]; omega_using [hsw])⟩)
  unfold t1One
  refine Piece.seq (B := fun s₀ s => TI p r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (t1S p r))
      ((vT1 (vPk p s₀) r).map fun c => ofInt (c * 2 ^ d : Nat)))
    (Verify.t1_piece (Y := YVE p p.pkLen) hP.unpackT1 0 (32 + 320 * r) 3 (oT1 p + 1024 * r)
      (by simp only [Bool.and_eq_true]; exact ⟨⟨vo, tr⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩)
      (by simp [YVE]) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' fr out => ⟨⟨h', fun j hj => keepPolyD hp (N := 80) (by simp [YVE])
        (by simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
            exact ⟨(Lay.okW_iff.mp (t1S_ok hF (by omega_using [hr, hj]))).1, (Lay.okW_iff.mp tr).1, sepT j (by omega_using [hr, hj]) (by omega_using [hj])⟩)
        fr (h.2 j hj)⟩, ?_⟩) ?_
  · have e := bytes_sub hp s.mem (a := 0) (o := 0) (k := 32 + 320 * r) (c := 320) (L := p.pkLen) (by omega_using [hr, hpk]) vall
      (by rw [Nat.zero_add]; exact vo)
    rw [Nat.zero_add, h.1.roBytes hp vall rfl] at e
    rw [e] at out
    exact out
  refine inPlace_piece (Y := YVE p p.pkLen) hP.ntt 3 (oT1 p + 1024 * r) 3 0
    (by simp only [Bool.and_eq_true]; exact ⟨⟨tr, ws⟩, sepW r hr⟩) (by simp [YVE]) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => ⟨h.1.1, h.2.1⟩) fun s₀ s s' hp h h' fr out => ⟨h', fun j hj => ?_⟩
  rcases (by omega_using [hj] : j < r ∨ j = r) with hj' | rfl
  · exact keepPolyD hp (N := 80) (by simp [YVE])
      (by simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨(Lay.okW_iff.mp (t1S_ok hF (by omega_using [hr, hj]))).1, ⟨(Lay.okW_iff.mp tr).1, sepT j (by omega_using [hr, hj]) (by omega_using [hj'])⟩,
            (Lay.okW_iff.mp ws).1, sepW j (by omega_using [hr, hj])⟩) fr (h.1.2 j hj')
  · rw [h.2.2] at out; exact out

theorem tS_addr (hF : VFacts p) {s₀ : State} (hp : TPre (YVE p p.pkLen) s₀) {r : Nat} (hr : r < p.k) :
    Buf.addr s₀ (t1S p r) = Buf.addr s₀ (sb (oT1 p) (1024 * p.k)) + BitVec.ofNat 64 (1024 * r) := by
  obtain hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  rw [Buf.addr_eq hp (Lay.okW_iff.mp (t1S_ok hF hr)).1,
    Buf.addr_eq hp (Lay.okW_iff.mp (okWS (p := p) (kl := p.pkLen) (o := oT1 p) (l := 1024 * p.k) (by omega_using [hr])
      (by simp only [oT1]; omega_using [hsw]))).1, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The body of `vg_mldsa*_verify`. -/
theorem entry_piece {P : Prims} (hP : PrimsOk P) (hF : VFacts p) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p (sb (oT1 p) (1024 * p.k))))) ht').isSome = true) :
    VE p p.pkLen (fun s₀ s => s = P0 s₀) (fun s₀ s' => Ctx (YVE p p.pkLen) s₀ s' ∧ VDone p s₀ s')
      (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) (.seq (seqR (t1One p P) 0 p.k)
        (callPR vS n f (coreArgs p (sb (oT1 p) (1024 * p.k)))))) := by
  obtain hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  refine (ldsc_piece (Y := YVE p p.pkLen) (ht := .block []) (by kernel_rfl)).seq ?_
  refine Piece.seq (B := TI p p.k) ((seqR_piece (I := fun r => TI p r) p.k 0
    fun r _ hr => t1One_piece hP hF (by omega_using [hr])).mono (fun _ _ _ h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
      fun _ _ _ h => by simpa using h) ?_
  exact core_piece hv hsp hst hF (Nat.le_refl _) _ rfl
    (Lay.okW_iff.mp (okWS (by omega_using [hk]) (by simp only [oT1]; omega_using [hsw]))).1
    (VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, .inr (Nat.le_of_eq (Nat.zero_add _))⟩)) tt
    fun s₀ s hp h => ⟨h.1, fun r hr => by rw [← tS_addr hF hp hr]; exact h.2 r hr⟩

/-! ## The contracts -/

theorem eaddr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem yve_alen (p : Params) (kl : Nat) :
    (YVE p kl).alen 0 = kl ∧ (YVE p kl).alen 1 = 64 ∧ (YVE p kl).alen 2 = p.sigLen ∧
      (YVE p kl).alen 3 = scratchWords p * 8 := ⟨rfl, rfl, rfl, rfl⟩

/-- The layout, from a 4-argument contract's precondition (`pre_of`). -/
theorem tpre_of {p : Params} {kl : Nat} {s₀ : State} (h1 : 136 ≤ (s₀.gpr .esp).toNat)
    (h2 : (s₀.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32)
    (h3 : s₀.rd = [⟨(arg s₀ 0).setWidth 64, kl⟩, ⟨(arg s₀ 1).setWidth 64, 64⟩, ⟨(arg s₀ 2).setWidth 64, p.sigLen⟩])
    (h4 : s₀.wr = [⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩, ⟨argAddr s₀ 0, 16⟩])
    (h5 : (⟨(arg s₀ 0).setWidth 64, kl⟩ : Region).Disjoint ⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩)
    (h6 : (⟨(arg s₀ 0).setWidth 64, kl⟩ : Region).Disjoint ⟨argAddr s₀ 0, 16⟩)
    (h7 : (⟨(arg s₀ 1).setWidth 64, 64⟩ : Region).Disjoint ⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩)
    (h8 : (⟨(arg s₀ 1).setWidth 64, 64⟩ : Region).Disjoint ⟨argAddr s₀ 0, 16⟩)
    (h9 : (⟨(arg s₀ 2).setWidth 64, p.sigLen⟩ : Region).Disjoint ⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩)
    (h10 : (⟨(arg s₀ 2).setWidth 64, p.sigLen⟩ : Region).Disjoint ⟨argAddr s₀ 0, 16⟩)
    (h11 : (⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩ : Region).Disjoint ⟨argAddr s₀ 0, 16⟩)
    (h12 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 0).setWidth 64, kl⟩)
    (h13 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 1).setWidth 64, 64⟩)
    (h14 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 2).setWidth 64, p.sigLen⟩)
    (h15 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩)
    (h17 : (below (E0 s₀) 136).Disjoint ⟨(arg s₀ 0).setWidth 64, kl⟩)
    (h18 : (below (E0 s₀) 136).Disjoint ⟨(arg s₀ 1).setWidth 64, 64⟩)
    (h19 : (below (E0 s₀) 136).Disjoint ⟨(arg s₀ 2).setWidth 64, p.sigLen⟩)
    (h20 : (below (E0 s₀) 136).Disjoint ⟨(arg s₀ 3).setWidth 64, scratchWords p * 8⟩)
    (h21 : (below (E0 s₀) 136).Disjoint ⟨argAddr s₀ 0, 16⟩)
    (h22 : (arg s₀ 0).toNat + kl ≤ 2 ^ 32) (h23 : (arg s₀ 1).toNat + 64 ≤ 2 ^ 32)
    (h24 : (arg s₀ 2).toNat + p.sigLen ≤ 2 ^ 32) (h25 : (arg s₀ 3).toNat + scratchWords p * 8 ≤ 2 ^ 32) :
    TPre (YVE p kl) s₀ := by
  obtain c4 : ∀ i, i < (YVE p kl).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [yve_n] at hi; omega_using [hi]
  refine ⟨h1, by show 16 ≤ 136; decide, by rw [yve_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h21, ?_, by show 3 < 4; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [argR, Lay.alen, YVE]
    · simp [argR, Lay.alen, YVE]
    · simp [argR, Lay.alen, YVE]
    · simp [YVE, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    any_goals simp [YVE, Lay.awr] at hw
    simp [argR, Lay.alen, YVE]
  · rw [h4]; simp [gR, Lay.n, YVE]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp [YVE, Lay.awr] at hw
    all_goals simp only [argR, YVE, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [h5, h7, h9, h5.symm, h7.symm, h9.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, gR, YVE, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    · exact h6.symm
    · exact h8.symm
    · exact h10.symm
    · exact h11.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, YVE, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [h12, h13, h14, h15]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, YVE, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [h17, h18, h19, h20]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [YVE, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [h22, h23, h24, h25]

theorem ePre_of {s₀ : State} (h : (verifyContract p X86.abi 136).pre s₀) : TPre (YVE p p.pkLen) s₀ := by
  sig_pre [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩ := h
  obtain hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
    simp only [below]; rw [Taint.sub_setWidth (by omega)]
  rw [hs] at h17 h18 h19 h20 h21
  exact tpre_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h17 h18 h19 h20 h21 h22 h23 h24 h25

theorem ePub_of {kl : Nat} {s₀ s₀' : State} (h : (verifyContract p X86.abi 136).pub s₀ s₀') :
    TPub (YVE p kl) (lkV p) s₀ s₀' := by
  sig_pub [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [yve_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkV, vPk, vMu, vSig, eaddr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMemV : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- The body of `vg_mldsa*_verify` never writes `esp`, if its core does not. -/
theorem entry_nosp {P : Prims} (hP : PrimsOk P) (p : Params) {n : String} {f : Prog isa} (hsp : NoSp f) :
    NoSp (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) (.seq (seqR (t1One p P) 0 p.k)
      (callPR vS n f (coreArgs p (sb (oT1 p) (1024 * p.k)))))) :=
  NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq
    (NoSp.seqR (fun _ => NoSp.seq (NoSp.callP hP.unpackT1.nosp) (NoSp.callP hP.ntt.nosp)) _ _) (NoSp.callPR hsp))

/-- `vg_mldsa*_verify` never writes `esp`, if its core does not. -/
theorem verifyEntry_nosp {P : Prims} (hP : PrimsOk P) (p : Params) {n : String} {f : Prog isa} (hsp : NoSp f) :
    NoSp (verifyEntry p P n f) := NoSp.leaf (entry_nosp hP p hsp)

/-- The body of `vg_mldsa*_verify_prepared` never writes `esp`, if its core does not. -/
theorem prepared_nosp (p : Params) {n : String} {f : Prog isa} (hsp : NoSp f) :
    NoSp (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))])
      (callPR vS n f (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩))) :=
  NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.callPR hsp)

/-- `vg_mldsa*_verify_prepared` never writes `esp`, if its core does not. -/
theorem verifyPrepared_nosp (p : Params) {n : String} {f : Prog isa} (hsp : NoSp f) :
    NoSp (verifyPrepared p n f) := NoSp.leaf (prepared_nosp p hsp)

/-- `vg_mldsa{44,65,87}_verify`, calling a core verified against `verifyCoreContract`,
is verified against `verifyContract`. -/
theorem entry_verified {P : Prims} (hP : PrimsOk P)
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p (sb (oT1 p) (1024 * p.k))))) ht').isSome = true) :
    Verified X86.target (verifyEntry p P n f) (verifyContract p X86.abi 136) := by
  obtain hF := vfacts hp
  refine Piece.verified (((topLeaf (entry_nosp hP p hsp) (entry_piece hP hF hv hsp hst tt)).pre_mono (fun _ h => ePre_of h)
    fun _ _ _ _ h => ePub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [sw_app, hax]
    unfold VDone at hd
    simp only [vPk, vMu, vSig, eaddr0] at hd
    exact hd
  · rcases hp with rfl | rfl | rfl
    · exact ⟨satState satMemV [⟨0, mlDsa44.pkLen⟩, ⟨0x1000, 64⟩, ⟨0x3000, mlDsa44.sigLen⟩]
        [⟨0x10000, scratchWords mlDsa44 * 8⟩, ⟨0x5004, 16⟩], by sig_sat_check [verifyContract, verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState, satMemV]⟩
    · exact ⟨satState satMemV [⟨0, mlDsa65.pkLen⟩, ⟨0x1000, 64⟩, ⟨0x3000, mlDsa65.sigLen⟩]
        [⟨0x10000, scratchWords mlDsa65 * 8⟩, ⟨0x5004, 16⟩], by sig_sat_check [verifyContract, verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState, satMemV]⟩
    · exact ⟨satState satMemV [⟨0, mlDsa87.pkLen⟩, ⟨0x1000, 64⟩, ⟨0x3000, mlDsa87.sigLen⟩]
        [⟨0x10000, scratchWords mlDsa87 * 8⟩, ⟨0x5004, 16⟩], by sig_sat_check [verifyContract, verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState, satMemV]⟩

/-! ## `vg_mldsa*_verify_prepared` -/

/-- The prepared public key on entry. -/
abbrev PPK (p : Params) (s₀ : State) : Prop := PreparedPublicKey p s₀.mem ((arg s₀ 0).setWidth 64)

theorem ppk_ok {o l : Nat} (hl : 0 < l) (h : o + l ≤ p.pkLen + 1024 * p.k) :
    (YVE p (preparedPublicKeyBytes p)).ok ⟨0, o, l⟩ = true :=
  okA (by decide) hl (by simp only [YVE, Lay.alen, List.getD_cons_zero, preparedPublicKeyBytes, Spec.MlDsa.n]; omega_using [h])

/-- Polynomial `r` of the prepared key, as the call of the core sees it. -/
theorem ppk_poly {s₀ s : State} (hp : TPre (YVE p (preparedPublicKeyBytes p)) s₀)
    (hc : Ctx (YVE p (preparedPublicKeyBytes p)) s₀ s) (hk : PPK p s₀) {r : Nat} (hr : r < p.k) :
    PolyIs s.mem (Buf.addr s₀ ⟨0, p.pkLen, 1024 * p.k⟩ + BitVec.ofNat 64 (1024 * r)) (t1Hat (vPk p s₀) r) := by
  obtain e := (Proof.MlDsa.preparedPublicKey_iff.mp hk) r hr
  obtain pk : bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen = vPk p s₀ := by simp only [vPk, eaddr0]
  rw [pk, PreparedKey.public_poly p _ hr] at e
  obtain hB := ppk_ok (p := p) (o := p.pkLen + 1024 * r) (l := 1024) (by decide) (by omega_using [hr])
  obtain a1 : (arg s₀ 0).setWidth 64 + BitVec.ofNat 64 (p.pkLen + 4 * Spec.MlDsa.n * r) =
      Buf.addr s₀ ⟨0, p.pkLen + 1024 * r, 1024⟩ := by
    rw [Buf.addr_eq hp hB]; simp only [Spec.MlDsa.n]
  obtain a2 : Buf.addr s₀ ⟨0, p.pkLen, 1024 * p.k⟩ + BitVec.ofNat 64 (1024 * r) =
      Buf.addr s₀ ⟨0, p.pkLen + 1024 * r, 1024⟩ := by
    rw [Buf.addr_eq hp hB, Buf.addr_eq hp (ppk_ok (by omega_using [hr]) (Nat.le_refl _)), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [a1] at e
  rw [a2]
  exact Proof.MlDsa.Verify.polyIs_congr (fun i hi => hc.ro hp hB rfl hi) e

/-- The body of `vg_mldsa*_verify_prepared`, with its precondition. -/
theorem prep_piece (hF : VFacts p) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩))) ht').isSome = true) :
    Piece (fun s => TPre (YVE p (preparedPublicKeyBytes p)) s ∧ PPK p s) (TPub (YVE p (preparedPublicKeyBytes p)) (lkV p))
      (fun s₀ s => s = P0 s₀) (fun s₀ s' => Ctx (YVE p (preparedPublicKeyBytes p)) s₀ s' ∧ VDone p s₀ s')
      (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))])
        (callPR vS n f (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩))) := by
  have hk := hF.k
  have hpk := hF.pk
  obtain hkl : p.pkLen ≤ preparedPublicKeyBytes p := by simp only [preparedPublicKeyBytes]; omega_using []
  obtain hcore := core_piece (n := n) (A := fun s₀ s => Ctx (YVE p (preparedPublicKeyBytes p)) s₀ s ∧ PPK p s₀)
    hv hsp hst hF hkl _ rfl (ppk_ok (by omega_using [hk]) (Nat.le_refl _))
    (VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)) tt
    fun s₀ s hp h => ⟨h.1, fun r hr => ppk_poly hp h.1 h.2 hr⟩
  obtain hl := (piece_pureV (PPK p) (ldsc_piece (Y := YVE p (preparedPublicKeyBytes p))
    (lk := lkV p) (ht := .block []) (by kernel_rfl))).seq hcore
  exact ⟨fun s₀ s h₀ ha => hl.wp s₀ s h₀.1 ⟨ha, h₀.2⟩, fun s₀ s₀' h₀ h₀' hq => (hl.ct s₀ s₀' h₀.1 h₀'.1 hq).mono
    (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩) fun _ _ h => h⟩

theorem pPre_of {s₀ : State} (h : (Proof.MlDsa.preparedVerifyContract p X86.abi 136).pre s₀) :
    TPre (YVE p (preparedPublicKeyBytes p)) s₀ ∧ PPK p s₀ := by
  sig_pre [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, kp⟩ := h
  obtain hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
    simp only [below]; rw [Taint.sub_setWidth (by omega)]
  rw [hs] at h17 h18 h19 h20 h21
  exact ⟨tpre_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h17 h18 h19 h20 h21 h22 h23 h24 h25, kp⟩

theorem pPub_of {s₀ s₀' : State} (h : (Proof.MlDsa.preparedVerifyContract p X86.abi 136).pub s₀ s₀') :
    TPub (YVE p (preparedPublicKeyBytes p)) (lkV p) s₀ s₀' := by
  sig_pub [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [yve_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkV, vPk, vMu, vSig, eaddr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

/-- `vg_mldsa{44,65,87}_verify_prepared`, calling a core verified against
`verifyCoreContract`, is verified against `preparedVerifyContract` (given
that its precondition can hold, which a run of
`vg_mldsa*_prepare_verifying_key` shows). -/
theorem prepared_verified (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩))) ht').isSome = true)
    (hsat : ∃ s, (Proof.MlDsa.preparedVerifyContract p X86.abi 136).pre s) :
    Verified X86.target (verifyPrepared p n f) (Proof.MlDsa.preparedVerifyContract p X86.abi 136) := by
  obtain hF := vfacts hp
  obtain hl := Piece.leaf (W (YVE p (preparedPublicKeyBytes p))) (prepared_nosp p (n := n) hsp)
    (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega_using [this]⟩) (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1)
    ((prep_piece hF hv hsp hst tt).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)
  refine Piece.verified ((hl.pre_mono (fun _ h => pPre_of h) fun _ _ _ _ h => pPub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) hsat
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
  rw [sw_app, hax]
  unfold VDone at hd
  simp only [vPk, vMu, vSig, eaddr0] at hd
  exact hd

end

end VG.Proof.MlDsa.X86.VerifyEntry

end

end

/-!
# ML-DSA on x86 (32-bit): the functions on `μ` and on messages, with encoded and prepared keys

Untrusted: everything here is checked by Lean. For each parameter set:

* `vg_mldsa*_sign` and `vg_mldsa*_sign_prepared` (`Sign/Entry.lean`), which
  call `vg_mldsa*_sign_core`, meet `signContract` and `preparedSignContract`
  (`sign44_verified`, `signPrepared44_verified`, …), and so `signKContract`
  of an encoded key and of a prepared one (`secretKey`); the same for
  verification (`Verify/Entry.lean`);
* `vg_mldsa*_sign_message` and `vg_mldsa*_sign_message_prepared` (the same
  code, calling the two functions on `μ`) meet `signMessageContract` and
  `preparedSignMessageContract`; `vg_mldsa*_verify_message_cached` and
  `vg_mldsa*_verify_message_prepared`, `verifyMessageCachedContract` and
  `preparedVerifyMessageContract`.

The preconditions with a prepared key hold of a key that
`vg_mldsa*_prepare_signing_key` or `vg_mldsa*_prepare_verifying_key` wrote
(`signPrepared_sat`, `verifyPrepared_sat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86.PreparedKey (above above_eq above_low above_readW secret_congr public_congr)
open VG.Impl.MlDsa.X86.Sign (signEntry signPrepared)
open VG.Impl.MlDsa.X86.Verify (verifyOf verifyPreparedOf)

/-! ## Prepared keys as `KeyArg`s -/

theorem bytes_pt {m m' : Mem} {a : Addr} {n : Nat} (h : bytesAt m' a n = bytesAt m a n) :
    ∀ i < n, m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i) := fun i hi => by
  have e := congrArg (fun l : List Byte => l[i]!) h
  rwa [Proof.MlKem.bytesAt_getElem! _ _ hi, Proof.MlKem.bytesAt_getElem! _ _ hi] at e

/-- A prepared private key. -/
abbrev secretKey (p : Params) : KeyArg := ⟨preparedSecretKeyBytes p, PreparedSecretKey p⟩
/-- A prepared public key. -/
abbrev publicKey (p : Params) : KeyArg := ⟨preparedPublicKeyBytes p, PreparedPublicKey p⟩

theorem secretKey_ok {p : Params} (hp : p ∈ params) : (secretKey p).Ok p.skLen := by
  refine ⟨(skLen_ge hp).1, by simp only [preparedSecretKeyBytes]; omega_using [], ?_,
    fun h k => secret_congr k (bytes_pt h)⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem publicKey_ok {p : Params} (hp : p ∈ params) : (publicKey p).Ok p.pkLen := by
  refine ⟨(pkLen_ge hp).1, by simp only [preparedPublicKeyBytes]; omega_using [], ?_,
    fun h k => public_congr k (bytes_pt h)⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- What `preparedVerifyMessageContract` requires of `pk` and `tr`. -/
abbrev preparedTr (p : Params) (m : Mem) (pk tr : Addr) : Prop :=
  PreparedPublicKey p m pk ∧ bytesAt m tr 64 = pkTr (bytesAt m pk p.pkLen)

theorem preparedSignContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.MlDsa.preparedSignContract p A stack = signKContract p (secretKey p) A stack := rfl
theorem preparedVerifyContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.MlDsa.preparedVerifyContract p A stack = verifyKContract p (publicKey p) A stack := rfl
theorem preparedSignMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    preparedSignMessageContract p A stack = signMessageKContract p (secretKey p) A stack := rfl
theorem preparedVerifyMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    preparedVerifyMessageContract p A stack =
      verifyMessageKContract p (preparedPublicKeyBytes p) (preparedTr p) A stack := rfl

/-! ## The preconditions with prepared keys can hold -/

/-- `satMemS`, with `sk` at `0x8000`. -/
def satMemSP : Mem := fun a => if a = 0x5005 then 0x80 else satMemS a

theorem signPrepared_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (signMessageKContract p (secretKey p) X86.abi 176).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.secret_at Verify.prims_ok hp3
  have hk : PreparedSecretKey p (above satMemSP m) 0x8000 := secret_congr hm fun i hi => above_eq
    (Nat.lt_of_lt_of_le hi (by rcases hp3 with rfl | rfl | rfl <;> decide))
  refine ⟨Proof.MlKem.X86.satState (above satMemSP m) [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, 32⟩] [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩], ?_⟩
  have a0 : ∀ τ : State, τ.mem = above satMemSP m → τ.gpr .esp = 0x5000 →
      arg τ 0 = 0x8000 ∧ arg τ 1 = 0x2000 ∧ arg τ 2 = 0 ∧ arg τ 3 = 0x2000 ∧ arg τ 4 = 0 ∧ arg τ 5 = 0x3000 ∧
        arg τ 6 = 0x6000 ∧ arg τ 7 = 0x10000 := by
    intro τ e he
    simp only [arg, argAddr, e, he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [above_readW]
    all_goals first | decide | kernel_rfl
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := a0 (Proof.MlKem.X86.satState (above satMemSP m)
    [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, 32⟩]
    [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) rfl rfl
  have ag : argAddr (Proof.MlKem.X86.satState (above satMemSP m) [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, 32⟩] [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) 0 = 0x5004 := rfl
  sig_pre [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, ag]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    and_intros
    all_goals first
      | exact hk
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

/-- `satMemC0`, with `pk` at `0x8000` and `tr` at `0x7800`. -/
def satMemVP0 : Mem := fun a => if a = 0x5005 then 0x80 else if a = 0x5021 then 0x78 else satMemC0 a

/-- `above satMemVP0 m`, with `tr = H(pk, 64)` of the key at `0x8000` at `0x7800`. -/
def satMemVP (p : Params) (m : Mem) : Mem := fun a =>
  if 0x7800 ≤ a.toNat ∧ a.toNat < 0x7840 then (pkTr (bytesAt m 0x8000 p.pkLen)).getD (a.toNat - 0x7800) 0
  else above satMemVP0 m a

theorem satMemVP_low {p : Params} {m : Mem} {x : Addr} (hx : x.toNat < 0x7800) : satMemVP p m x = satMemVP0 x := by
  simp only [satMemVP, show ¬(0x7800 ≤ x.toNat ∧ x.toNat < 0x7840) by omega_using [hx], ↓reduceIte]
  exact above_low (a := satMemVP0) (m := m) (by omega_using [hx])

theorem satMemVP_high {p : Params} {m : Mem} {i : Nat} (hi : i < 2 ^ 32) :
    satMemVP p m (0x8000 + BitVec.ofNat 64 i) = m (0x8000 + BitVec.ofNat 64 i) := by
  have e : (0x8000 + BitVec.ofNat 64 i : Addr).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega_using [hi]
  simp only [satMemVP, e, show ¬(0x7800 ≤ 0x8000 + i ∧ 0x8000 + i < 0x7840) by omega_using [], ↓reduceIte]
  exact above_eq hi

theorem verifyPrepared_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (verifyMessageKContract p (preparedPublicKeyBytes p) (preparedTr p) X86.abi 172).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.public_at Verify.prims_ok hp3
  have hb : preparedPublicKeyBytes p < 2 ^ 32 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hk : PreparedPublicKey p (satMemVP p m) 0x8000 := public_congr hm fun i hi => satMemVP_high (by omega_using [hb, hi])
  have hkb : bytesAt (satMemVP p m) 0x8000 p.pkLen = bytesAt m 0x8000 p.pkLen :=
    Proof.MlKem.bytesAt_congr fun i hi => satMemVP_high (by simp only [preparedPublicKeyBytes] at hb; omega_using [hb, hi])
  have htr : bytesAt (satMemVP p m) 0x7800 64 = pkTr (bytesAt (satMemVP p m) 0x8000 p.pkLen) := by
    rw [hkb]
    apply Proof.MlKem.bytesAt_eq (H_length _ _)
    intro i hi
    have he : ((0x7800 : Addr) + BitVec.ofNat 64 i).toNat = 0x7800 + i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega_using [hi]
    simp only [satMemVP, he, show 0x7800 ≤ 0x7800 + i ∧ 0x7800 + i < 0x7840 by omega_using [hi], and_self, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [pkTr, H_length]; omega_using [hi]), Option.getD_some]
    rfl
  refine ⟨Proof.MlKem.X86.satState (satMemVP p m) [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩,
    ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩] [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩], ?_⟩
  have a0 : ∀ τ : State, τ.mem = satMemVP p m → τ.gpr .esp = 0x5000 →
      arg τ 0 = 0x8000 ∧ arg τ 1 = 0x2000 ∧ arg τ 2 = 0 ∧ arg τ 3 = 0x2000 ∧ arg τ 4 = 0 ∧ arg τ 5 = 0x3000 ∧
        arg τ 6 = 0x10000 ∧ arg τ 7 = 0x7800 := by
    intro τ e he
    simp only [arg, argAddr, e, he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [Mem.readW_congr (m' := satMemVP0) fun j hj => satMemVP_low ?_]
    all_goals first | kernel_rfl | (revert hj; revert j; decide)
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := a0 (Proof.MlKem.X86.satState (satMemVP p m)
    [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩]
    [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) rfl rfl
  have ag : argAddr (Proof.MlKem.X86.satState (satMemVP p m) [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩] [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) 0 = 0x5004 := rfl
  sig_pre [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, ag]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    and_intros
    all_goals first
      | exact hk
      | exact htr
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

/-! ## ML-DSA-44 -/

private theorem core44_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44) := KeyGen.NoSp.leaf Sign.body44_nosp

theorem sign44_verified : Verified X86.target (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) (signContract mlDsa44 X86.abi 136) :=
  SignEntry.entry_verified (.inl rfl) Sign.signCore44_verified core44_noSp (by lit_decide)
    (by native_taint_decide)

theorem signPrepared44_verified :
    Verified X86.target (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) (Proof.MlDsa.preparedSignContract mlDsa44 X86.abi 136) :=
  SignEntry.prepared_verified (.inl rfl) Sign.signCore44_verified core44_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inl rfl))

theorem verify44_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify44 (verifyContract mlDsa44 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inl rfl) Verify.verifyCore44_verified (Verify.verify_nosp _)
    (by lit_decide) (by native_taint_decide)

theorem verifyPrepared44_verified :
    Verified X86.target (verifyPreparedOf mlDsa44 "mldsa44") (Proof.MlDsa.preparedVerifyContract mlDsa44 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inl rfl) Verify.verifyCore44_verified (Verify.verify_nosp _) (by lit_decide)
    (by native_taint_decide) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inl rfl))

theorem sign44Fn : SignFn mlDsa44 (plainKey mlDsa44.skLen) (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) :=
  ⟨by rw [← signContract_eq]; exact sign44_verified, SignEntry.signEntry_nosp _ core44_noSp, by lit_decide⟩
theorem signPrepared44Fn : SignFn mlDsa44 (secretKey mlDsa44) (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared44_verified, SignEntry.signPrepared_nosp _ core44_noSp, by lit_decide⟩
theorem verify44Fn : VerifyFn mlDsa44 (plainKey mlDsa44.pkLen) Impl.MlDsa.X86.Verify.verify44 :=
  ⟨by rw [← verifyContract_eq]; exact verify44_verified, VerifyEntry.verifyEntry_nosp Verify.prims_ok _ (Verify.verify_nosp _), by lit_decide⟩
theorem verifyPrepared44Fn : VerifyFn mlDsa44 (publicKey mlDsa44) (verifyPreparedOf mlDsa44 "mldsa44") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared44_verified, VerifyEntry.verifyPrepared_nosp _ (Verify.verify_nosp _), by lit_decide⟩

theorem signMessage44_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.entryName "mldsa44") (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) mlDsa44) (signMessageContract mlDsa44 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_self ..))) sign44Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_self ..))

theorem signMessagePrepared44_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedEntryName "mldsa44") (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa44)) mlDsa44)
      (preparedSignMessageContract mlDsa44 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_self ..)) signPrepared44Fn (by native_taint_decide) (signPrepared_sat (.inl rfl))

theorem verifyMessageCached44_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.entryName "mldsa44") Impl.MlDsa.X86.Verify.verify44 mlDsa44)
      (verifyMessageCachedContract mlDsa44 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_self ..))) (fun h => ⟨trivial, h⟩) verify44Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_self ..))

theorem verifyMessagePrepared44_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName "mldsa44") (verifyPreparedOf mlDsa44 "mldsa44") mlDsa44)
      (preparedVerifyMessageContract mlDsa44 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_self ..)) (fun h => h) verifyPrepared44Fn
    (by native_taint_decide) (verifyPrepared_sat (.inl rfl))

/-! ## ML-DSA-65 -/

private theorem core65_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65) := KeyGen.NoSp.leaf Sign.body65_nosp

theorem sign65_verified : Verified X86.target (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) (signContract mlDsa65 X86.abi 136) :=
  SignEntry.entry_verified (.inr (.inl rfl)) Sign.signCore65_verified core65_noSp (by lit_decide)
    (by native_taint_decide)

theorem signPrepared65_verified :
    Verified X86.target (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) (Proof.MlDsa.preparedSignContract mlDsa65 X86.abi 136) :=
  SignEntry.prepared_verified (.inr (.inl rfl)) Sign.signCore65_verified core65_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inr (.inl rfl)))

theorem verify65_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify65 (verifyContract mlDsa65 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inr (.inl rfl)) Verify.verifyCore65_verified (Verify.verify_nosp _)
    (by lit_decide) (by native_taint_decide)

theorem verifyPrepared65_verified :
    Verified X86.target (verifyPreparedOf mlDsa65 "mldsa65") (Proof.MlDsa.preparedVerifyContract mlDsa65 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inr (.inl rfl)) Verify.verifyCore65_verified (Verify.verify_nosp _) (by lit_decide)
    (by native_taint_decide) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inr (.inl rfl)))

theorem sign65Fn : SignFn mlDsa65 (plainKey mlDsa65.skLen) (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) :=
  ⟨by rw [← signContract_eq]; exact sign65_verified, SignEntry.signEntry_nosp _ core65_noSp, by lit_decide⟩
theorem signPrepared65Fn : SignFn mlDsa65 (secretKey mlDsa65) (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared65_verified, SignEntry.signPrepared_nosp _ core65_noSp, by lit_decide⟩
theorem verify65Fn : VerifyFn mlDsa65 (plainKey mlDsa65.pkLen) Impl.MlDsa.X86.Verify.verify65 :=
  ⟨by rw [← verifyContract_eq]; exact verify65_verified, VerifyEntry.verifyEntry_nosp Verify.prims_ok _ (Verify.verify_nosp _), by lit_decide⟩
theorem verifyPrepared65Fn : VerifyFn mlDsa65 (publicKey mlDsa65) (verifyPreparedOf mlDsa65 "mldsa65") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared65_verified, VerifyEntry.verifyPrepared_nosp _ (Verify.verify_nosp _), by lit_decide⟩

theorem signMessage65_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.entryName "mldsa65") (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) mlDsa65) (signMessageContract mlDsa65 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) sign65Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem signMessagePrepared65_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedEntryName "mldsa65") (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa65)) mlDsa65)
      (preparedSignMessageContract mlDsa65 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_of_mem _ (List.mem_cons_self ..))) signPrepared65Fn (by native_taint_decide) (signPrepared_sat (.inr (.inl rfl)))

theorem verifyMessageCached65_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.entryName "mldsa65") Impl.MlDsa.X86.Verify.verify65 mlDsa65)
      (verifyMessageCachedContract mlDsa65 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (fun h => ⟨trivial, h⟩) verify65Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem verifyMessagePrepared65_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName "mldsa65") (verifyPreparedOf mlDsa65 "mldsa65") mlDsa65)
      (preparedVerifyMessageContract mlDsa65 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (fun h => h) verifyPrepared65Fn
    (by native_taint_decide) (verifyPrepared_sat (.inr (.inl rfl)))

/-! ## ML-DSA-87 -/

private theorem core87_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87) := KeyGen.NoSp.leaf Sign.body87_nosp

theorem sign87_verified : Verified X86.target (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) (signContract mlDsa87 X86.abi 136) :=
  SignEntry.entry_verified (.inr (.inr rfl)) Sign.signCore87_verified core87_noSp (by lit_decide)
    (by native_taint_decide)

theorem signPrepared87_verified :
    Verified X86.target (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) (Proof.MlDsa.preparedSignContract mlDsa87 X86.abi 136) :=
  SignEntry.prepared_verified (.inr (.inr rfl)) Sign.signCore87_verified core87_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inr (.inr rfl)))

theorem verify87_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify87 (verifyContract mlDsa87 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inr (.inr rfl)) Verify.verifyCore87_verified (Verify.verify_nosp _)
    (by lit_decide) (by native_taint_decide)

theorem verifyPrepared87_verified :
    Verified X86.target (verifyPreparedOf mlDsa87 "mldsa87") (Proof.MlDsa.preparedVerifyContract mlDsa87 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inr (.inr rfl)) Verify.verifyCore87_verified (Verify.verify_nosp _) (by lit_decide)
    (by native_taint_decide) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inr (.inr rfl)))

theorem sign87Fn : SignFn mlDsa87 (plainKey mlDsa87.skLen) (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) :=
  ⟨by rw [← signContract_eq]; exact sign87_verified, SignEntry.signEntry_nosp _ core87_noSp, by lit_decide⟩
theorem signPrepared87Fn : SignFn mlDsa87 (secretKey mlDsa87) (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared87_verified, SignEntry.signPrepared_nosp _ core87_noSp, by lit_decide⟩
theorem verify87Fn : VerifyFn mlDsa87 (plainKey mlDsa87.pkLen) Impl.MlDsa.X86.Verify.verify87 :=
  ⟨by rw [← verifyContract_eq]; exact verify87_verified, VerifyEntry.verifyEntry_nosp Verify.prims_ok _ (Verify.verify_nosp _), by lit_decide⟩
theorem verifyPrepared87Fn : VerifyFn mlDsa87 (publicKey mlDsa87) (verifyPreparedOf mlDsa87 "mldsa87") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared87_verified, VerifyEntry.verifyPrepared_nosp _ (Verify.verify_nosp _), by lit_decide⟩

theorem signMessage87_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.entryName "mldsa87") (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) mlDsa87) (signMessageContract mlDsa87 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) sign87Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem signMessagePrepared87_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedEntryName "mldsa87") (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Impl.MlDsa.X86.Sign.prims mlDsa87)) mlDsa87)
      (preparedSignMessageContract mlDsa87 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) signPrepared87Fn (by native_taint_decide) (signPrepared_sat (.inr (.inr rfl)))

theorem verifyMessageCached87_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.entryName "mldsa87") Impl.MlDsa.X86.Verify.verify87 mlDsa87)
      (verifyMessageCachedContract mlDsa87 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (fun h => ⟨trivial, h⟩) verify87Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem verifyMessagePrepared87_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedEntryName "mldsa87") (verifyPreparedOf mlDsa87 "mldsa87") mlDsa87)
      (preparedVerifyMessageContract mlDsa87 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (fun h => h) verifyPrepared87Fn
    (by native_taint_decide) (verifyPrepared_sat (.inr (.inr rfl)))

end VG.Proof.MlDsa.X86.Message
