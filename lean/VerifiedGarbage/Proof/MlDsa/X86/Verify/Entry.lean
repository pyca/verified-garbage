module

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Entry
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Prim
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inv
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Omega

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
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

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
  have o0 : (YVE p kl).ok ⟨0, 0, p.pkLen⟩ = true := okA (by decide) (by omega) (by simp [YVE, Lay.alen]; omega)
  have o1 : (YVE p kl).ok ⟨1, 0, 64⟩ = true := okA (by decide) (by decide) (by simp [YVE, Lay.alen])
  have o2 : (YVE p kl).ok ⟨2, 0, p.sigLen⟩ = true := okA (by decide) (by have := hF.ct; omega) (by simp [YVE, Lay.alen])
  have w3 : (YVE p kl).okW ⟨3, 0, oT1 p⟩ = true := okWS (by simp only [oT1]; omega) (by simp only [oT1]; omega)
  have r3 := (Lay.okW_iff.mp w3).1
  refine callPR_pieceK (lk := lkV p) (K := 96) (coreArgs p t) [⟨0, 0, p.pkLen⟩, ⟨1, 0, 64⟩, ⟨2, 0, p.sigLen⟩, t]
    [⟨3, 0, oT1 p⟩] (fun _ _ h => h) hv hsp hst (by simp [coreArgs])
    (by simp [coreArgs]) (by simp [coreArgs, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, o0, o1, o2, r3, ht])
    (by simp [YVE]) (by simp [YVE]) (by simp [o0, o1, o2, ht]) (by simp [w3]) tt
    (fun s₀ s hp h => (hA s₀ s hp h).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨hc, ht1⟩ := hA s₀ s hp ha
    have hpkb : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have hkp : T1In p e.mem (Buf.addr s₀ t) (bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen) := by
      intro r hr
      rw [hpkb, PreparedKey.public_poly p _ hr]
      exact Proof.MlDsa.Verify.polyIs_congr (off_congr (he.mem _ ht) (by rw [htl]; omega)) (ht1 r hr)
    obtain ⟨b₀, b₀', b₀'', b₀f⟩ := he.bufK hp (by simp [coreArgs]) o0 (K := 96) (by simp [YVE])
    obtain ⟨b₁, b₁', b₁'', b₁f⟩ := he.bufK hp (by simp [coreArgs]) o1 (K := 96) (by simp [YVE])
    obtain ⟨b₂, b₂', b₂'', b₂f⟩ := he.bufK hp (by simp [coreArgs]) o2 (K := 96) (by simp [YVE])
    obtain ⟨b₃, b₃', b₃'', b₃f⟩ := he.bufK hp (by simp [coreArgs]) r3 (K := 96) (by simp [YVE])
    obtain ⟨b₄, b₄', b₄'', b₄f⟩ := he.bufK hp (by simp [coreArgs]) ht (K := 96) (by simp [YVE])
    obtain ⟨x₁, x₂⟩ := he.selfK hp (by simp [coreArgs]) (K := 96) (by simp [YVE])
    obtain ⟨en, hE⟩ := he.espNat hp (by simp [YVE]) (by simp [coreArgs])
    have hE2 : 120 ≤ (E1 s₀).toNat := by
      rw [E1_nat s₀ hp.E0_big]; have := hp.sp; simp only [YVE] at this; omega
    have d03 := Buf.disj hp o0 r3 (by simp [Lay.sep, YVE, Lay.awr])
    have d13 := Buf.disj hp o1 r3 (by simp [Lay.sep, YVE, Lay.awr])
    have d23 := Buf.disj hp o2 r3 (by simp [Lay.sep, YVE, Lay.awr])
    have dt3 := Buf.disj hp ht r3 hts
    have dt3' := dt3.symm
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
    have a₃ := he.arg 3 (by simp [coreArgs])
    have a₄ := he.arg 4 (by simp [coreArgs])
    have aa := he.argAddr0
    have e3 : (scratchWords p - 128 * p.k) * 8 = oT1 p := by simp only [oT1]; omega
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
    have l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = vMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    have l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    have l₁' : bytesAt e'.mem (Buf.addr s₀' ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o0)]; exact hc'.roBytes hp' o0 rfl
    have l₂' : bytesAt e'.mem (Buf.addr s₀' ⟨1, 0, 64⟩) 64 = vMu s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o1)]; exact hc'.roBytes hp' o1 rfl
    have l₃' : bytesAt e'.mem (Buf.addr s₀' ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o2)]; exact hc'.roBytes hp' o2 rfl
    have hl := hq.2.2
    simp only [lkV] at hl
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
    have a₀' := he'.arg 0 (by simp [coreArgs])
    have a₁' := he'.arg 1 (by simp [coreArgs])
    have a₂' := he'.arg 2 (by simp [coreArgs])
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [verifyCoreContract, verifyCoreSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a₀, a₁, a₂, a₀', a₁', a₂', coreArgs, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Impl.MlDsa.X86.KeyGen.Arg.val, Buf.addr] at *
    refine ⟨esp, ?_, hq.ptr o0, hq.ptr o1, hq.ptr o2, ags 3 (by simp), ags 4 (by simp)⟩
    simp only [l₁, l₂, l₃, l₁', l₂', l₃', hl]
  · obtain ⟨hc, -⟩ := hA s₀ s hp ha
    have l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen = vPk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = vMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    have l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen = vSig p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
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
  have hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  exact okWS (by decide) (by simp only [oT1]; omega)

theorem ws_ok (hF : VFacts p) : (YVE p p.pkLen).okW (sb 0 1024) = true := by
  have hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  exact okWS (by decide) (by omega)

/-- Row `r` of `t̂₁`. -/
theorem t1One_piece {P : Prims} (hP : PrimsOk P) (hF : VFacts p) {r : Nat} (hr : r < p.k) :
    VE p p.pkLen (TI p r) (TI p (r + 1)) (t1One p P r) := by
  have hk := hF.k; have hsw := hF.sw; have hscr := hF.scr; have hpk := hF.pk
  have ws := ws_ok hF
  have tr := t1S_ok hF hr
  have vo : (YVE p p.pkLen).ok ⟨0, 32 + 320 * r, 320⟩ = true :=
    okA (by decide) (by decide) (by simp only [YVE, Lay.alen, List.getD_cons_zero]; omega)
  have vall : (YVE p p.pkLen).ok ⟨0, 0, p.pkLen⟩ = true :=
    okA (by decide) (by omega) (by simp only [YVE, Lay.alen, List.getD_cons_zero]; omega)
  have sepT : ∀ j < p.k, j ≠ r → (YVE p p.pkLen).sep (t1S p j) (t1S p r) = true := fun j hj hne =>
    VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, by simp only; omega⟩)
  have sepW : ∀ j < p.k, (YVE p p.pkLen).sep (t1S p j) (sb 0 1024) = true := fun j hj =>
    VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, .inr (by simp only [oT1]; omega)⟩)
  unfold t1One
  refine Piece.seq (B := fun s₀ s => TI p r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (t1S p r))
      ((vT1 (vPk p s₀) r).map fun c => ofInt (c * 2 ^ d : Nat)))
    (Verify.t1_piece (Y := YVE p p.pkLen) hP.unpackT1 0 (32 + 320 * r) 3 (oT1 p + 1024 * r)
      (by simp only [Bool.and_eq_true]; exact ⟨⟨vo, tr⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩)
      (by simp [YVE]) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' fr out => ⟨⟨h', fun j hj => keepPolyD hp (N := 80) (by simp [YVE])
        (by simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
            exact ⟨(Lay.okW_iff.mp (t1S_ok hF (by omega))).1, (Lay.okW_iff.mp tr).1, sepT j (by omega) (by omega)⟩)
        fr (h.2 j hj)⟩, ?_⟩) ?_
  · have e := bytes_sub hp s.mem (a := 0) (o := 0) (k := 32 + 320 * r) (c := 320) (L := p.pkLen) (by omega) vall
      (by rw [Nat.zero_add]; exact vo)
    rw [Nat.zero_add, h.1.roBytes hp vall rfl] at e
    rw [e] at out
    exact out
  refine inPlace_piece (Y := YVE p p.pkLen) hP.ntt 3 (oT1 p + 1024 * r) 3 0
    (by simp only [Bool.and_eq_true]; exact ⟨⟨tr, ws⟩, sepW r hr⟩) (by simp [YVE]) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => ⟨h.1.1, h.2.1⟩) fun s₀ s s' hp h h' fr out => ⟨h', fun j hj => ?_⟩
  rcases (by omega : j < r ∨ j = r) with hj' | rfl
  · exact keepPolyD hp (N := 80) (by simp [YVE])
      (by simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨(Lay.okW_iff.mp (t1S_ok hF (by omega))).1, ⟨(Lay.okW_iff.mp tr).1, sepT j (by omega) (by omega)⟩,
            (Lay.okW_iff.mp ws).1, sepW j (by omega)⟩) fr (h.1.2 j hj')
  · rw [h.2.2] at out; exact out

theorem tS_addr (hF : VFacts p) {s₀ : State} (hp : TPre (YVE p p.pkLen) s₀) {r : Nat} (hr : r < p.k) :
    Buf.addr s₀ (t1S p r) = Buf.addr s₀ (sb (oT1 p) (1024 * p.k)) + BitVec.ofNat 64 (1024 * r) := by
  have hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  rw [Buf.addr_eq hp (Lay.okW_iff.mp (t1S_ok hF hr)).1,
    Buf.addr_eq hp (Lay.okW_iff.mp (okWS (p := p) (kl := p.pkLen) (o := oT1 p) (l := 1024 * p.k) (by omega)
      (by simp only [oT1]; omega))).1, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The body of `vg_mldsa*_verify`. -/
theorem entry_piece {P : Prims} (hP : PrimsOk P) (hF : VFacts p) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p (sb (oT1 p) (1024 * p.k))))) ht').isSome = true) :
    VE p p.pkLen (fun s₀ s => s = P0 s₀) (fun s₀ s' => Ctx (YVE p p.pkLen) s₀ s' ∧ VDone p s₀ s')
      (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) (.seq (seqR (t1One p P) 0 p.k)
        (callPR vS n f (coreArgs p (sb (oT1 p) (1024 * p.k)))))) := by
  have hk := hF.k; have hsw := hF.sw; have hscr := hF.scr
  refine (ldsc_piece (Y := YVE p p.pkLen) (ht := .block []) (by kernel_rfl)).seq ?_
  refine Piece.seq (B := TI p p.k) ((seqR_piece (I := fun r => TI p r) p.k 0
    fun r _ hr => t1One_piece hP hF (by omega)).mono (fun _ _ _ h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
      fun _ _ _ h => by simpa using h) ?_
  exact core_piece hv hsp hst hF (Nat.le_refl _) _ rfl
    (Lay.okW_iff.mp (okWS (by omega) (by simp only [oT1]; omega))).1
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
  have c4 : ∀ i, i < (YVE p kl).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [yve_n] at hi; omega
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
  have hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
    simp only [below]; rw [Taint.sub_setWidth (by omega)]
  rw [hs] at h17 h18 h19 h20 h21
  exact tpre_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h17 h18 h19 h20 h21 h22 h23 h24 h25

theorem ePub_of {kl : Nat} {s₀ s₀' : State} (h : (verifyContract p X86.abi 136).pub s₀ s₀') :
    TPub (YVE p kl) (lkV p) s₀ s₀' := by
  sig_pub [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [yve_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkV, vPk, vMu, vSig, eaddr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMemV : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- `vg_mldsa{44,65,87}_verify`, calling a core verified against `verifyCoreContract`,
is verified against `verifyContract`. -/
theorem entry_verified {P : Prims} (hP : PrimsOk P)
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {n : String} {f : Prog isa}
    (hv : Verified X86.target f (verifyCoreContract p X86.abi 96)) (hsp : NoSp f) (hst : stackUse f ≤ 96)
    {ht' : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs 3 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p (sb (oT1 p) (1024 * p.k))))) ht').isSome = true)
    (hsp' : NoSp (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) (.seq (seqR (t1One p P) 0 p.k)
        (callPR vS n f (coreArgs p (sb (oT1 p) (1024 * p.k))))))) :
    Verified X86.target (verifyEntry p P n f) (verifyContract p X86.abi 136) := by
  have hF := vfacts hp
  refine Piece.verified (((topLeaf hsp' (entry_piece hP hF hv hsp hst tt)).pre_mono (fun _ h => ePre_of h)
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
  okA (by decide) hl (by simp only [YVE, Lay.alen, List.getD_cons_zero, preparedPublicKeyBytes, Spec.MlDsa.n]; omega)

/-- Polynomial `r` of the prepared key, as the call of the core sees it. -/
theorem ppk_poly {s₀ s : State} (hp : TPre (YVE p (preparedPublicKeyBytes p)) s₀)
    (hc : Ctx (YVE p (preparedPublicKeyBytes p)) s₀ s) (hk : PPK p s₀) {r : Nat} (hr : r < p.k) :
    PolyIs s.mem (Buf.addr s₀ ⟨0, p.pkLen, 1024 * p.k⟩ + BitVec.ofNat 64 (1024 * r)) (t1Hat (vPk p s₀) r) := by
  have e := (Proof.MlDsa.preparedPublicKey_iff.mp hk) r hr
  have pk : bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen = vPk p s₀ := by simp only [vPk, eaddr0]
  rw [pk, PreparedKey.public_poly p _ hr] at e
  have hB := ppk_ok (p := p) (o := p.pkLen + 1024 * r) (l := 1024) (by decide) (by omega)
  have a1 : (arg s₀ 0).setWidth 64 + BitVec.ofNat 64 (p.pkLen + 4 * Spec.MlDsa.n * r) =
      Buf.addr s₀ ⟨0, p.pkLen + 1024 * r, 1024⟩ := by
    rw [Buf.addr_eq hp hB]; simp only [Spec.MlDsa.n]
  have a2 : Buf.addr s₀ ⟨0, p.pkLen, 1024 * p.k⟩ + BitVec.ofNat 64 (1024 * r) =
      Buf.addr s₀ ⟨0, p.pkLen + 1024 * r, 1024⟩ := by
    rw [Buf.addr_eq hp hB, Buf.addr_eq hp (ppk_ok (by omega) (Nat.le_refl _)), BitVec.add_assoc,
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
  have hkl : p.pkLen ≤ preparedPublicKeyBytes p := by simp only [preparedPublicKeyBytes]; omega
  have hcore := core_piece (n := n) (A := fun s₀ s => Ctx (YVE p (preparedPublicKeyBytes p)) s₀ s ∧ PPK p s₀)
    hv hsp hst hF hkl _ rfl (ppk_ok (by omega) (Nat.le_refl _))
    (VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)) tt
    fun s₀ s hp h => ⟨h.1, fun r hr => ppk_poly hp h.1 h.2 hr⟩
  have hl := (piece_pureV (PPK p) (ldsc_piece (Y := YVE p (preparedPublicKeyBytes p))
    (lk := lkV p) (ht := .block []) (by kernel_rfl))).seq hcore
  exact ⟨fun s₀ s h₀ ha => hl.wp s₀ s h₀.1 ⟨ha, h₀.2⟩, fun s₀ s₀' h₀ h₀' hq => (hl.ct s₀ s₀' h₀.1 h₀'.1 hq).mono
    (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩) fun _ _ h => h⟩

theorem pPre_of {s₀ : State} (h : (Proof.MlDsa.preparedVerifyContract p X86.abi 136).pre s₀) :
    TPre (YVE p (preparedPublicKeyBytes p)) s₀ ∧ PPK p s₀ := by
  sig_pre [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, kp⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
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
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
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
    (hsp' : NoSp (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))])
        (callPR vS n f (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩))))
    (hsat : ∃ s, (Proof.MlDsa.preparedVerifyContract p X86.abi 136).pre s) :
    Verified X86.target (verifyPrepared p n f) (Proof.MlDsa.preparedVerifyContract p X86.abi 136) := by
  have hF := vfacts hp
  have hl := Piece.leaf (W (YVE p (preparedPublicKeyBytes p))) hsp'
    (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega⟩) (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1)
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
