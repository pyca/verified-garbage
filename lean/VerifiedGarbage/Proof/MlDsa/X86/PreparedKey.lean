module

public import VerifiedGarbage.Impl.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inv
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Prim
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ML-DSA on x86 (32-bit): preparing keys

`vg_mldsa*_prepare_signing_key` and `vg_mldsa*_prepare_verifying_key`
(`Impl/MlDsa/X86/PreparedKey.lean`), proven as the other top-level functions
on x86, in a layout of their own (`YP`: the key, of `kl` bytes, read;
`prepared`, of `pl` bytes, and the 1024 bytes of `scratch`, written; 96
bytes of stack): the copy of the key (`start_piece`), then each polynomial
(`PI`: the key copied, and the polynomials so far).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.PreparedKey

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.PreparedKey
open VG.Impl.MlDsa.X86.KeyGen (setArgs callP seqR)
open VG.Impl.MlDsa.X86.Verify (Prims)
open VG.Proof.MlDsa.X86.Verify (PrimsOk)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The layout, for a key of `kl` bytes and a prepared key of `pl`. -/
def YP (kl pl : Nat) : Lay := ⟨[(kl, false), (pl, true), (1024, true)], 2, 96⟩

/-- Nothing but the pointers. -/
abbrev lkP : State → List Byte := fun _ => []

/-- The pieces. -/
abbrev PP (kl pl : Nat) := Piece (TPre (YP kl pl)) (TPub (YP kl pl) lkP)

section
variable {kl pl : Nat}

theorem yp_n : (YP kl pl).n = 3 := rfl

theorem okK {o l : Nat} (hl : 0 < l) (h : o + l ≤ kl) : (YP kl pl).ok ⟨0, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨by show 0 < 3; decide, hl, h⟩

theorem okP {o l : Nat} (hl : 0 < l) (h : o + l ≤ pl) : (YP kl pl).okW ⟨1, o, l⟩ = true :=
  Lay.okW_iff.mpr ⟨Lay.ok_iff.mpr ⟨by show 1 < 3; decide, hl, h⟩, rfl⟩

theorem okS : (YP kl pl).okW ⟨2, 0, 1024⟩ = true :=
  Lay.okW_iff.mpr ⟨Lay.ok_iff.mpr ⟨by show 2 < 3; decide, by decide, Nat.le_refl _⟩, rfl⟩

/-- The key on entry. -/
abbrev keyOf (kl : Nat) (s₀ : State) : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, kl⟩) kl

/-- After polynomial `i`: the key copied, and the polynomials `f j` for `j < i`. -/
def PI (kl : Nat) (f : State → Nat → Poly) (i : Nat) (s₀ s : State) : Prop :=
  Ctx (YP kl pl) s₀ s ∧ bytesAt s.mem (Buf.addr s₀ ⟨1, 0, kl⟩) kl = keyOf kl s₀ ∧
    ∀ j < i, PolyIs s.mem (Buf.addr s₀ ⟨1, kl + 1024 * j, 1024⟩) (f s₀ j)

/-- `esi ← scratch`, and the key copied. -/
theorem start_piece (f : State → Nat → Poly) (hk : 0 < kl) (h4 : 4 * (kl / 4) = kl) (hkl : kl ≤ pl)
    (hk30 : kl / 4 < 2 ^ 30) :
    PP kl pl (fun s₀ s => s = P0 s₀) (PI (pl := pl) kl f 0) (start kl) := by
  unfold start
  refine (ldsc_piece (Y := YP kl pl) (ht := .block []) (by kernel_rfl)).seq ?_
  have hc : ((YP kl pl).ok ⟨0, 0, 4 * (kl / 4)⟩ && (YP kl pl).okW ⟨1, 0, 4 * (kl / 4)⟩ &&
      (YP kl pl).sep ⟨0, 0, 4 * (kl / 4)⟩ ⟨1, 0, 4 * (kl / 4)⟩) = true := by
    rw [h4]
    simp only [Bool.and_eq_true]
    exact ⟨⟨okK (pl := pl) (o := 0) (l := kl) hk (by omega), okP (kl := kl) (o := 0) (l := kl) hk (by omega)⟩,
      VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
  refine copyW_piece (Y := YP kl pl) 0 0 1 0 (kl / 4) (by omega) hk30 hc (h₁ := .block []) (by kernel_rfl)
    (by native_taint_decide) (fun _ _ _ h => h) fun s₀ s s' hp h h' fr hb => ⟨h', ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [h4] at hb
  rw [hb]
  exact h.roBytes hp (okK (o := 0) (l := kl) hk (by omega)) rfl

/-- Slot `i`, and `prepared`'s other slots and copy of the key, apart. -/
theorem slot_sep {i j : Nat} (h : i ≠ j) : (YP kl pl).sep (slot kl i) (slot kl j) = true :=
  VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl,
    show kl + 1024 * i + 1024 ≤ kl + 1024 * j ∨ kl + 1024 * j + 1024 ≤ kl + 1024 * i by omega⟩)

theorem key_slot_sep {i : Nat} : (YP kl pl).sep ⟨1, 0, kl⟩ (slot kl i) = true :=
  VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, .inl (show 0 + kl ≤ kl + 1024 * i by omega)⟩)

/-- A step that writes slot `i` and `scratch` keeps the copy of the key and the other slots. -/
theorem PI.keep {f : State → Nat → Poly} {i : Nat} {s₀ s s' : State} (hp : TPre (YP kl pl) s₀) (hk : 0 < kl)
    (hi : kl + 1024 * (i + 1) ≤ pl) (h : PI (pl := pl) kl f i s₀ s) (h' : Ctx (YP kl pl) s₀ s')
    (fr : Frame (FR s₀ [slot kl i, ⟨2, 0, 1024⟩] 80) s.mem s'.mem) : PI (pl := pl) kl f i s₀ s' := by
  have hi1 : kl + 1024 * i + 1024 ≤ pl := by rw [Nat.mul_succ, ← Nat.add_assoc] at hi; exact hi
  have hsl : (YP kl pl).ok (slot kl i) = true :=
    (Lay.okW_iff.mp (okP (kl := kl) (o := kl + 1024 * i) (l := 1024) (by decide) hi1)).1
  have hs : (YP kl pl).ok ⟨2, 0, 1024⟩ = true := (Lay.okW_iff.mp okS).1
  refine ⟨h', ?_, fun j hj => ?_⟩
  · have hap : (YP kl pl).apart ⟨1, 0, kl⟩ [slot kl i, ⟨2, 0, 1024⟩] = true := by
      simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨(Lay.okW_iff.mp (okP (kl := kl) (o := 0) (l := kl) hk (by omega))).1, ⟨hsl, key_slot_sep⟩, hs,
        VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
    rw [keepBytes hp (N := 80) (by simp [YP]) hap fr]
    exact h.2.1
  · have hap : (YP kl pl).apart ⟨1, kl + 1024 * j, 1024⟩ [slot kl i, ⟨2, 0, 1024⟩] = true := by
      simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨(Lay.okW_iff.mp (okP (kl := kl) (o := kl + 1024 * j) (l := 1024) (by decide) (by rw [Nat.mul_succ, ← Nat.add_assoc] at hi; exact Nat.le_trans (by omega) hi))).1,
        ⟨hsl, slot_sep (by omega)⟩, hs,
        VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
    exact keepPolyD hp (N := 80) (by simp [YP]) hap fr (h.2.2 j hj)

/-- The bytes of the key at `o`, from the start. -/
theorem key_slice {s₀ s : State} (hp : TPre (YP kl pl) s₀) (h : Ctx (YP kl pl) s₀ s) {o l : Nat} (hl : 0 < l)
    (hol : o + l ≤ kl) : bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((keyOf kl s₀).drop o).take l := by
  have e := bytes_sub hp s₀.mem (a := 0) (o := 0) (k := o) (c := l) (L := kl) hol (okK (by omega) (by omega))
    (by rw [Nat.zero_add]; exact okK hl hol)
  rw [Nat.zero_add] at e
  rw [h.roBytes hp (okK hl hol) rfl]
  exact e

/-! ## `vg_mldsa*_prepare_verifying_key` -/

/-- Polynomial `r` of a prepared public key. -/
theorem publicPoly_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hpk : p.pkLen = 32 + 320 * p.k) {r : Nat}
    (hr : r < p.k) (hpl : p.pkLen + 1024 * p.k ≤ pl) :
    PP p.pkLen pl (PI (pl := pl) p.pkLen (fun s₀ j => Verify.t1Hat (keyOf p.pkLen s₀) j) r)
      (PI (pl := pl) p.pkLen (fun s₀ j => Verify.t1Hat (keyOf p.pkLen s₀) j) (r + 1)) (publicPoly P p r) := by
  have hsl : (YP p.pkLen pl).okW (slot p.pkLen r) = true := okP (o := p.pkLen + 1024 * r) (l := 1024) (by decide) (by omega)
  have hv : (YP p.pkLen pl).ok ⟨0, 32 + 320 * r, 320⟩ = true := okK (o := 32 + 320 * r) (l := 320) (by decide) (by omega)
  unfold publicPoly
  refine Piece.seq (B := fun s₀ s => PI (pl := pl) p.pkLen (fun s₀ j => Verify.t1Hat (keyOf p.pkLen s₀) j) r s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ (slot p.pkLen r)) ((Verify.vT1 (keyOf p.pkLen s₀) r).map fun c => ofInt (c * 2 ^ d : Nat)))
    (Verify.t1_piece (Y := YP p.pkLen pl) hP.unpackT1 0 (32 + 320 * r) 1 (p.pkLen + 1024 * r)
      (by simp only [Bool.and_eq_true]
          exact ⟨⟨hv, hsl⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩)
      (by simp [YP]) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' fr out => ⟨PI.keep hp (by omega) (by omega) h h' (fr.sub fun x hx => ?_), ?_⟩) ?_
  · simp only [FR, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | h
    · exact ⟨_, .inl rfl, fun _ h => h⟩
    · exact ⟨_, .inr (.inr (.inl rfl)), fun _ h => h⟩
    · exact absurd h List.not_mem_nil
  · rw [key_slice hp h.1 (by decide) (by omega)] at out
    exact out
  refine inPlace_piece (Y := YP p.pkLen pl) hP.ntt 1 (p.pkLen + 1024 * r) 2 0
    (by simp only [Bool.and_eq_true]
        exact ⟨⟨hsl, okS⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inl rfl⟩)⟩)
    (by simp [YP]) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => ⟨h.1.1, h.2.1⟩) fun s₀ s s' hp h h' fr out => ?_
  have hk := PI.keep hp (by omega) (by omega) h.1 h' fr
  refine ⟨hk.1, hk.2.1, fun j hj => ?_⟩
  rcases (by omega : j < r ∨ j = r) with hj' | rfl
  · exact hk.2.2 j hj'
  · rw [h.2.2] at out; exact out

/-! ## The contracts -/

theorem paddr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- The layout, from a 3-argument contract's precondition. -/
theorem tpre_of {s₀ : State} (h1 : 96 ≤ (s₀.gpr .esp).toNat)
    (h2 : (s₀.gpr .esp).toNat + 4 + 12 ≤ 2 ^ 32)
    (h3 : s₀.rd = [⟨(arg s₀ 0).setWidth 64, kl⟩])
    (h4 : s₀.wr = [⟨(arg s₀ 1).setWidth 64, pl⟩, ⟨(arg s₀ 2).setWidth 64, 1024⟩, ⟨argAddr s₀ 0, 12⟩])
    (d01 : (⟨(arg s₀ 0).setWidth 64, kl⟩ : Region).Disjoint ⟨(arg s₀ 1).setWidth 64, pl⟩)
    (d02 : (⟨(arg s₀ 0).setWidth 64, kl⟩ : Region).Disjoint ⟨(arg s₀ 2).setWidth 64, 1024⟩)
    (d0g : (⟨(arg s₀ 0).setWidth 64, kl⟩ : Region).Disjoint ⟨argAddr s₀ 0, 12⟩)
    (d12 : (⟨(arg s₀ 1).setWidth 64, pl⟩ : Region).Disjoint ⟨(arg s₀ 2).setWidth 64, 1024⟩)
    (d1g : (⟨(arg s₀ 1).setWidth 64, pl⟩ : Region).Disjoint ⟨argAddr s₀ 0, 12⟩)
    (d2g : (⟨(arg s₀ 2).setWidth 64, 1024⟩ : Region).Disjoint ⟨argAddr s₀ 0, 12⟩)
    (r0 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 0).setWidth 64, kl⟩)
    (r1 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 1).setWidth 64, pl⟩)
    (r2 : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 2).setWidth 64, 1024⟩)
    (s0 : (below (E0 s₀) 96).Disjoint ⟨(arg s₀ 0).setWidth 64, kl⟩)
    (s1 : (below (E0 s₀) 96).Disjoint ⟨(arg s₀ 1).setWidth 64, pl⟩)
    (s2 : (below (E0 s₀) 96).Disjoint ⟨(arg s₀ 2).setWidth 64, 1024⟩)
    (sg : (below (E0 s₀) 96).Disjoint ⟨argAddr s₀ 0, 12⟩)
    (f0 : (arg s₀ 0).toNat + kl ≤ 2 ^ 32) (f1 : (arg s₀ 1).toNat + pl ≤ 2 ^ 32)
    (f2 : (arg s₀ 2).toNat + 1024 ≤ 2 ^ 32) :
    TPre (YP kl pl) s₀ := by
  have c3 : ∀ i, i < (YP kl pl).n → i = 0 ∨ i = 1 ∨ i = 2 := fun i hi => by rw [yp_n] at hi; omega
  refine ⟨h1, by show 16 ≤ 96; decide, by rw [yp_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 2 < 3; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c3 i hi with rfl | rfl | rfl
    · simp [argR, Lay.alen, YP]
    all_goals simp [YP, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c3 i hi with rfl | rfl | rfl
    · simp [YP, Lay.awr] at hw
    · simp [argR, Lay.alen, YP]
    · simp [argR, Lay.alen, YP]
  · rw [h4]; simp [gR, Lay.n, YP]
  · intro i hi j hj hne hw
    rcases c3 i hi with rfl | rfl | rfl <;> rcases c3 j hj with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [argR, YP, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [d01, d02, d01.symm, d12, d02.symm, d12.symm]
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;>
      simp only [argR, gR, YP, Lay.alen, Lay.n, List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
        List.length_nil]
    · exact d0g.symm
    · exact d1g.symm
    · exact d2g.symm
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [argR, YP, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [r0, r1, r2]
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [argR, YP, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [s0, s1, s2]
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [YP, Lay.alen, List.getD_cons_zero, List.getD_cons_succ]
    exacts [f0, f1, f2]

end

section
variable {p : Params}

theorem pub_pre_of {s₀ : State} (h : (preparePublicKeyContract p X86.abi 96).pre s₀) :
    TPre (YP p.pkLen (preparedPublicKeyBytes p)) s₀ := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d01, d02, d0g, d12, d1g, d2g, r0, r1, r2, -, s0, s1, s2, sg, f0, f1, f2⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth (by omega)]
  rw [hs] at s0 s1 s2 sg
  exact tpre_of h1 h2 h3 h4 d01 d02 d0g d12 d1g d2g r0 r1 r2 s0 s1 s2 sg f0 f1 f2

theorem sec_pre_of {s₀ : State} (h : (prepareSecretKeyContract p X86.abi 96).pre s₀) :
    TPre (YP p.skLen (preparedSecretKeyBytes p)) s₀ := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d01, d02, d0g, d12, d1g, d2g, r0, r1, r2, -, s0, s1, s2, sg, f0, f1, f2⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth (by omega)]
  rw [hs] at s0 s1 s2 sg
  exact tpre_of h1 h2 h3 h4 d01 d02 d0g d12 d1g d2g r0 r1 r2 s0 s1 s2 sg f0 f1 f2

theorem pub_pub_of {s₀ s₀' : State} (h : (preparePublicKeyContract p X86.abi 96).pub s₀ s₀') :
    TPub (YP p.pkLen (preparedPublicKeyBytes p)) lkP s₀ s₀' := by
  sig_pub [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄⟩ := h
  refine ⟨e₁, fun i hi => ?_, rfl⟩
  rw [yp_n] at hi
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  exacts [e₂, e₃, e₄]

theorem sec_pub_of {s₀ s₀' : State} (h : (prepareSecretKeyContract p X86.abi 96).pub s₀ s₀') :
    TPub (YP p.skLen (preparedSecretKeyBytes p)) lkP s₀ s₀' := by
  sig_pub [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄⟩ := h
  refine ⟨e₁, fun i hi => ?_, rfl⟩
  rw [yp_n] at hi
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  exacts [e₂, e₃, e₄]

/-- Memory with the arguments `0`, `0x8000` and `0x20000` at `0x5004`. -/
def satMemP : Mem := fun a => if a = 0x5009 then 0x80 else if a = 0x500e then 2 else 0

/-- Polynomial `i` of `prepared`, as the contract addresses it. -/
theorem slot_addr {kl pl : Nat} {s₀ : State} (hp : TPre (YP kl pl) s₀) {i : Nat} (hi : kl + 1024 * i + 1024 ≤ pl) :
    Buf.addr s₀ ⟨1, kl + 1024 * i, 1024⟩ = (arg s₀ 1).setWidth 64 + BitVec.ofNat 64 (kl + 4 * n * i) := by
  rw [Buf.addr_eq hp (Lay.okW_iff.mp (okP (kl := kl) (o := kl + 1024 * i) (l := 1024) (by decide) hi)).1]
  simp only [n]

/-- `vg_mldsa{44,65,87}_prepare_verifying_key`, with the primitives `P`, is verified against `preparePublicKeyContract`. -/
theorem public_verified {P : Prims} (hP : PrimsOk P) (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified X86.target (preparePublic P p) (preparePublicKeyContract p X86.abi 96) := by
  have hF := Verify.vfacts hp3
  have hpk := hF.pk
  have hk := hF.k
  have hpl : p.pkLen + 1024 * p.k ≤ preparedPublicKeyBytes p := by simp only [preparedPublicKeyBytes, n]; omega
  have hb : PP p.pkLen (preparedPublicKeyBytes p) (fun s₀ s => s = P0 s₀)
      (fun s₀ s => Ctx (YP p.pkLen (preparedPublicKeyBytes p)) s₀ s ∧
        PI (pl := preparedPublicKeyBytes p) p.pkLen (fun s₀ j => Verify.t1Hat (keyOf p.pkLen s₀) j) p.k s₀ s)
      (.seq (start p.pkLen) (seqR (publicPoly P p) 0 p.k)) :=
    (start_piece _ (by omega) (by omega) (by omega) (by omega)).seq
      ((seqR_piece (I := fun r => PI (pl := preparedPublicKeyBytes p) p.pkLen
        (fun s₀ j => Verify.t1Hat (keyOf p.pkLen s₀) j) r) p.k 0
        fun r _ hr => publicPoly_piece hP hpk (by omega) hpl).mono (fun _ _ _ h => h)
        fun _ _ _ h => ⟨h.1, by simpa using h⟩)
  have hsp : NoSp (.seq (start p.pkLen) (seqR (publicPoly P p) 0 p.k)) := by
    unfold start publicPoly nttSlot
    exact NoSp.seq (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.of_all (by kernel_rfl)))
      (NoSp.seqR (fun r => NoSp.seq (NoSp.callP hP.unpackT1.nosp) (NoSp.callP hP.ntt.nosp)) _ _)
  refine Piece.verified (((topLeaf hsp hb).pre_mono (fun _ h => pub_pre_of h)
    fun _ _ _ _ h => pub_pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pub_pre_of h₀
    obtain ⟨habi, -, -, s, ⟨-, hk', hpol⟩, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have e1 : bytesAt s'.mem ((arg s₀ 1).setWidth 64) p.pkLen = bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen := by
      rw [hm]; simpa only [keyOf, paddr0] using hk'
    refine ⟨e1, fun i hi => ?_⟩
    rw [e1, PreparedKey.public_poly p _ hi, ← slot_addr hp (by omega)]
    refine Proof.MlDsa.polyStored_iff.mpr ?_
    rw [hm]
    have := hpol i hi
    simp only [keyOf, paddr0] at this
    exact this
  · rcases hp3 with rfl | rfl | rfl
    · exact ⟨satState satMemP [⟨0, 1312⟩] [⟨0x8000, 5408⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩
    · exact ⟨satState satMemP [⟨0, 1952⟩] [⟨0x8000, 8096⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩
    · exact ⟨satState satMemP [⟨0, 2592⟩] [⟨0x8000, 10784⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [preparePublicKeyContract, preparePublicKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩

/-! ## `vg_mldsa*_prepare_signing_key` -/

/-- Polynomial `i` of a prepared private key, from its piece of the key. -/
theorem secret_val (key : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    (preparedSecretPolys p key)[i]! = ntt (toRq (bitUnpack ((key.drop (secretPiece p i).1).take (secretPiece p i).2.1)
      (secretPiece p i).2.2.1 (secretPiece p i).2.2.2)) := by
  unfold secretPiece
  by_cases h1 : i < p.ℓ
  · simp only [show i < p.ℓ + p.k from by omega, ↓reduceIte]
    rw [PreparedKey.secret_s1 p _ h1]; rfl
  by_cases h2 : i < p.ℓ + p.k
  · simp only [h2, ↓reduceIte]
    have e := PreparedKey.secret_s2 p key (i := i - p.ℓ) (by omega)
    rw [show p.ℓ + (i - p.ℓ) = i by omega] at e
    rw [e]
    unfold Sign.s2F
    rw [show 128 + Sign.lenS p * p.ℓ + Sign.lenS p * (i - p.ℓ) = 128 + sLen p * i by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)]]
  · simp only [h2, ↓reduceIte]
    have e := PreparedKey.secret_t0 p key (i := i - p.ℓ - p.k) (by omega)
    rw [show p.ℓ + p.k + (i - p.ℓ - p.k) = i by omega] at e
    rw [e]
    unfold Sign.t0F
    rw [show 128 + Sign.lenS p * p.ℓ + Sign.lenS p * p.k + 32 * d * (i - p.ℓ - p.k) =
      128 + sLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k) by rw [Nat.mul_add, ← Nat.add_assoc]; rfl]
    rfl

/-- The piece of the key of polynomial `i`: within the key, and an unpacking `BitUnpack` handles. -/
theorem piece_ok (ps : VG.Proof.MlDsa.X86.Sign.PS p) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    0 < (secretPiece p i).2.1 ∧ (secretPiece p i).1 + (secretPiece p i).2.1 ≤ p.skLen ∧
      ((secretPiece p i).2.2.1, (secretPiece p i).2.2.2) ∈ Proof.MlDsa.bitPackParams ∧
      (secretPiece p i).2.1 = 32 * bitlen ((secretPiece p i).2.2.1 + (secretPiece p i).2.2.2) := by
  have hk := ps.hk; have hl := ps.hl; have hsk := ps.hskLen
  have hs := ps.hsLen
  have hη1 := ps.hη.1
  have hη2 := ps.hη.2.1
  have e : sLen p = VG.Impl.MlDsa.X86.Sign.sLen p := rfl
  unfold secretPiece
  rw [e]
  generalize VG.Impl.MlDsa.X86.Sign.sLen p = S at hsk hs hη2
  by_cases h2 : i < p.ℓ + p.k
  · simp only [h2, ↓reduceIte]
    refine ⟨by rcases hs with h | h <;> omega, ?_, hη1, hη2⟩
    have : S * i + S ≤ S * (p.ℓ + p.k) := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
    generalize S * (p.ℓ + p.k) = X at this hsk
    omega
  · simp only [h2, ↓reduceIte]
    refine ⟨by decide, ?_, ps.ht0.1, ps.ht0.2⟩
    generalize S * (p.ℓ + p.k) = X at hsk ⊢
    omega

/-- Polynomial `i` of a prepared private key. -/
theorem secretPoly_piece {pl : Nat} {P : Prims} (hP : PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {i : Nat}
    (hi : i < p.ℓ + 2 * p.k) (hpl : p.skLen + 1024 * (p.ℓ + 2 * p.k) ≤ pl) :
    PP p.skLen pl (PI (pl := pl) p.skLen (fun s₀ j => (preparedSecretPolys p (keyOf p.skLen s₀))[j]!) i)
      (PI (pl := pl) p.skLen (fun s₀ j => (preparedSecretPolys p (keyOf p.skLen s₀))[j]!) (i + 1))
      (secretPoly P p i) := by
  obtain ⟨hL0, hLk, hab, hL⟩ := piece_ok ps hi
  have hsk : 0 < p.skLen := by have := ps.hskLen; omega
  have hsl : (YP p.skLen pl).okW (slot p.skLen i) = true :=
    okP (o := p.skLen + 1024 * i) (l := 1024) (by decide) (by omega)
  have hv : (YP p.skLen pl).ok ⟨0, (secretPiece p i).1, (secretPiece p i).2.1⟩ = true := okK hL0 hLk
  unfold secretPoly
  refine Piece.seq (B := fun s₀ s => PI (pl := pl) p.skLen (fun s₀ j => (preparedSecretPolys p (keyOf p.skLen s₀))[j]!) i s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ (slot p.skLen i)) (toRq (bitUnpack (((keyOf p.skLen s₀).drop (secretPiece p i).1).take
        (secretPiece p i).2.1) (secretPiece p i).2.2.1 (secretPiece p i).2.2.2)))
    (Verify.bu_piece (Y := YP p.skLen pl) hP.bitUnpack 0 (secretPiece p i).1 (secretPiece p i).2.1
      (secretPiece p i).2.2.1 (secretPiece p i).2.2.2 1 (p.skLen + 1024 * i) hab hL
      (by simp only [Bool.and_eq_true]
          exact ⟨⟨hv, hsl⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩)
      (by simp [YP]) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' fr out => ⟨PI.keep hp hsk (by omega) h h' (fr.sub fun x hx => ?_), ?_⟩) ?_
  · simp only [FR, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | h
    · exact ⟨_, .inl rfl, fun _ h => h⟩
    · exact ⟨_, .inr (.inr (.inl rfl)), fun _ h => h⟩
    · exact absurd h List.not_mem_nil
  · rw [key_slice hp h.1 hL0 hLk] at out
    exact out
  refine inPlace_piece (Y := YP p.skLen pl) hP.ntt 1 (p.skLen + 1024 * i) 2 0
    (by simp only [Bool.and_eq_true]
        exact ⟨⟨hsl, okS⟩, VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inr ⟨by simp, .inl rfl⟩)⟩)
    (by simp [YP]) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => ⟨h.1.1, h.2.1⟩) fun s₀ s s' hp h h' fr out => ?_
  have hk := PI.keep hp hsk (by omega) h.1 h' fr
  refine ⟨hk.1, hk.2.1, fun j hj => ?_⟩
  rcases (by omega : j < i ∨ j = i) with hj' | rfl
  · exact hk.2.2 j hj'
  · rw [h.2.2] at out
    show PolyIs _ _ (preparedSecretPolys p (keyOf p.skLen s₀))[j]!
    rw [secret_val _ hi]
    exact out

/-- `vg_mldsa{44,65,87}_prepare_signing_key`, with the primitives `P`, is verified against `prepareSecretKeyContract`. -/
theorem secret_verified {P : Prims} (hP : PrimsOk P) (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified X86.target (prepareSecret P p) (prepareSecretKeyContract p X86.abi 96) := by
  have ps := VG.Proof.MlDsa.X86.Sign.PS.of hp3
  have hk := ps.hk
  have hskl := ps.hskLen
  have hsk : 0 < p.skLen := by omega
  have hpl : p.skLen + 1024 * (p.ℓ + 2 * p.k) ≤ preparedSecretKeyBytes p := by
    simp only [preparedSecretKeyBytes, n]; omega
  have h4 : 4 * (p.skLen / 4) = p.skLen := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hb : PP p.skLen (preparedSecretKeyBytes p) (fun s₀ s => s = P0 s₀)
      (fun s₀ s => Ctx (YP p.skLen (preparedSecretKeyBytes p)) s₀ s ∧
        PI (pl := preparedSecretKeyBytes p) p.skLen (fun s₀ j => (preparedSecretPolys p (keyOf p.skLen s₀))[j]!)
          (p.ℓ + 2 * p.k) s₀ s)
      (.seq (start p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k))) :=
    (start_piece _ hsk h4 (by omega) (by rcases hp3 with rfl | rfl | rfl <;> decide)).seq
      ((seqR_piece (I := fun r => PI (pl := preparedSecretKeyBytes p) p.skLen
        (fun s₀ j => (preparedSecretPolys p (keyOf p.skLen s₀))[j]!) r) (p.ℓ + 2 * p.k) 0
        fun r _ hr => secretPoly_piece hP ps (by omega) hpl).mono (fun _ _ _ h => h)
        fun _ _ _ h => ⟨h.1, by simpa using h⟩)
  have hsp : NoSp (.seq (start p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k))) := by
    unfold start secretPoly nttSlot
    exact NoSp.seq (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.of_all (by kernel_rfl)))
      (NoSp.seqR (fun r => NoSp.seq (NoSp.callP hP.bitUnpack.nosp) (NoSp.callP hP.ntt.nosp)) _ _)
  refine Piece.verified (((topLeaf hsp hb).pre_mono (fun _ h => sec_pre_of h)
    fun _ _ _ _ h => sec_pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := sec_pre_of h₀
    obtain ⟨habi, -, -, s, ⟨-, hk', hpol⟩, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have e1 : bytesAt s'.mem ((arg s₀ 1).setWidth 64) p.skLen = bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen := by
      rw [hm]; simpa only [keyOf, paddr0] using hk'
    refine ⟨e1, fun i hi => ?_⟩
    rw [e1, ← slot_addr hp (by omega)]
    refine Proof.MlDsa.polyStored_iff.mpr ?_
    rw [hm]
    have := hpol i hi
    simp only [keyOf, paddr0] at this
    exact this
  · rcases hp3 with rfl | rfl | rfl
    · exact ⟨satState satMemP [⟨0, 2560⟩] [⟨0x8000, 14848⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩
    · exact ⟨satState satMemP [⟨0, 4032⟩] [⟨0x8000, 21440⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩
    · exact ⟨satState satMemP [⟨0, 4896⟩] [⟨0x8000, 28448⟩, ⟨0x20000, 1024⟩, ⟨0x5004, 12⟩],
        by sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, satState, satMemP]⟩

end

end VG.Proof.MlDsa.X86.PreparedKey
