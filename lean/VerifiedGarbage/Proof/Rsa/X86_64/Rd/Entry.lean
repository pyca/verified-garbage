module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Args
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_recover_primes_det` on x86-64: the entry and the failure path

`rpPre`: the precondition on the registers and the stack (`rdContract`'s
but for `e_len ≤ 8`), and `RpCtx`, what it gives (`rpCtx_of`). The entry
and the check of the modulus (`rpHead_ok'`) leave `RpPre`; zeros and 0 if
the key is refused (`rpFail_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- `fail`: zeros to `p` and `q`, 0 returned, and the saved registers
restored. -/
theorem rpFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (ha : RpArgs s.mem B k el dl pP pQ pN pE pD sv) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 31)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa fail s fun t =>
      (∀ i < k, t.mem (pP + BitVec.ofNat 64 i) = 0) ∧ (∀ i < k, t.mem (pQ + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have hn := hs.nowrap
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs hdi hZ (by decide) (by decide) ha.p ha.k hk1 hk2 oP)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oP.sep x₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (zeroOut_ok hs₁ hdi₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.q)
    (by rw [w₁ _ (by decide)]; exact ha.k) hk1 hk2 ⟨fun i hi => by rw [k₁.2.2]; exact oQ.wr i hi, oQ.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oQ.sep x₂
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hw : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [w₂ i hi, w₁ i hi]
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = 0 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  rw [hm]
  refine ⟨fun i hi => ?_, z₂, hax, fun i hi => ?_, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1],
    kk.gpr (by decide)⟩
  · rw [x₂ _ (fun j hj => a i hi j hj)]
    exact z₁ i hi
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (ha.saved 0 (by decide))
    · exact h1.trans (ha.saved 1 (by decide))
    · exact h2.trans (ha.saved 2 (by decide))
    · exact h3.trans (ha.saved 3 (by decide))
    · exact h4.trans (ha.saved 4 (by decide))
    · exact h5.trans (ha.saved 5 (by decide))

end VG.Proof.Rsa.X86_64

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

/-- The inputs as numbers. -/
abbrev RpIn.N (I : RpIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev RpIn.E (I : RpIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev RpIn.D (I : RpIn) : Nat := Spec.Rsa.os2ip I.db

/-- What `main` needs on entry. -/
structure RpPre (I : RpIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  rdi : s.gpr .rdi = I.B
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  L : RpLens I
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : Apart I.pP I.k I.pQ I.k
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

/-- The factors written, or 0. -/
def fstOr : Option (Nat × Nat) → Nat
  | some v => v.1
  | none => 0

def sndOr : Option (Nat × Nat) → Nat
  | some v => v.2
  | none => 0

end VG.Proof.Rsa.X86_64

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- The precondition, on the registers and the stack, of
`vg_rsa_recover_primes_det(p = rdi, p_len = rsi, q = rdx, q_len = rcx,
n = r8, n_len = r9, e = [rsp + 8], e_len = [rsp + 16], d = [rsp + 24],
d_len = [rsp + 32], scratch = [rsp + 40], scratch_len = [rsp + 48])`
but for `e_len ≤ 8`. -/
def rpPre : State → Prop := fun s =>
  let p : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let q : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let n : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let e : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let d : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
  let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 48⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧
    s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
    p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
    q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
    n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
    ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint d ∧
    ret.Disjoint scr ∧ ret.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
    (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
    Spec.Rsa.lenValid (s.gpr .r9).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .r9).toNat ∧
    (s.gpr .rcx).toNat = (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
    (stackArg s 1).toNat ≤ (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
    (stackArg s 3).toNat ≤ (s.gpr .r9).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r9).toNat ≤ (stackArg s 5).toNat

/-! ## The entry -/

theorem rpEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 40 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sP) .rdi, .store (hdr11 sQ) .rdx, .store (hdr11 Impl.Bignum.X86_64.Public.sN) .r8,
    .store (hdr11 Impl.Bignum.X86_64.Public.sK) .r9] : List Instr) ++
    (crtPairs [(0, Impl.Bignum.X86_64.Public.sE), (1, Impl.Bignum.X86_64.Public.sElen), (2, sD), (3, sDl)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def rpEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) : Mem :=
  (((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sQ)) vq).writeW (off B (8 * Impl.Bignum.X86_64.Public.sN)) vn).writeW
    (off B (8 * Impl.Bignum.X86_64.Public.sK)) vk

/-- The header after the entry's stores. -/
def rpEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) : Mem :=
  ((((rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk).writeW (off B (8 * Impl.Bignum.X86_64.Public.sE)) ve).writeW
    (off B (8 * Impl.Bignum.X86_64.Public.sElen)) vel).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem rpEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) :
    Outside B 0 (8 * 32) m (rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk) := by
  unfold rpEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem rpEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) :
    let m' := rpEntryMem m B v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧
    word m' B (8 * Impl.Bignum.X86_64.Public.sN) = vn ∧ word m' B (8 * Impl.Bignum.X86_64.Public.sK) = vk ∧
    word m' B (8 * Impl.Bignum.X86_64.Public.sE) = ve ∧ word m' B (8 * Impl.Bignum.X86_64.Public.sElen) = vel ∧
    word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' rpEntryMem rpEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 4) in `rdi`. -/
theorem rpEntry_ok {s : State} {B : Addr} (hB : stackArg s 4 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 5, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem B (8 * sP) = s.gpr .rdi ∧ word t.mem B (8 * sQ) = s.gpr .rdx ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sN) = s.gpr .r8 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sK) = s.gpr .r9 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sE) = stackArg s 0 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = stackArg s 1 ∧
      word t.mem B (8 * sD) = stackArg s 2 ∧ word t.mem B (8 * sDl) = stackArg s 3 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
  have hB' : s.mem.readW (stackArgAddr s 4) 64 = B := hB
  have ha4 := ha 4 (by decide)
  rw [rpEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = rpEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e4, ha4, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sP (by decide),
      hw sQ (by decide), hw Impl.Bignum.X86_64.Public.sN (by decide), hw Impl.Bignum.X86_64.Public.sK (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact rpEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = rpEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho⟩ :=
    rpEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3)
  refine ⟨hdi, fun i hi => ?_, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state. -/
def rpIn (s : State) : RpIn where
  B := stackArg s 4
  Z := (stackArg s 5).toNat * 8
  k := (s.gpr .r9).toNat
  el := (stackArg s 1).toNat
  dl := (stackArg s 3).toNat
  pP := s.gpr .rdi
  pQ := s.gpr .rdx
  pN := s.gpr .r8
  pE := stackArg s 0
  pD := stackArg s 2
  sv i := s.gpr (saved.getD i .rax)
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  eb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
  W := s.wr
  sp := s.gpr .rsp

/-- What `Recover.code` uses of its contract's precondition. -/
structure RpCtx (s : State) : Prop where
  L : RpLens (rpIn s)
  rsi : (s.gpr .rsi).toNat = (s.gpr .r9).toNat
  rcx : (s.gpr .rcx).toNat = (s.gpr .r9).toNat
  hs : Scr s (stackArg s 4) ((stackArg s 5).toNat * 8)
  ha : ∀ j < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 5, ∀ m', Outside (stackArg s 4) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .r8) (rpIn s).nb
  e : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (stackArg s 0) (rpIn s).eb
  d : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (stackArg s 2) (rpIn s).db
  oP : OutOk s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .rdi) (s.gpr .r9).toNat
  oQ : OutOk s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .rdx) (s.gpr .r9).toNat
  a : Apart (s.gpr .rdi) (s.gpr .r9).toNat (s.gpr .rdx) (s.gpr .r9).toNat
  hret : ∀ b < 8, (stackArg s 5).toNat * 8 ≤ ofs (stackArg s 4) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ j < (s.gpr .r9).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j) ∧
    (∀ j < (s.gpr .r9).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 j)

theorem rpCtx_of {s : State} (h : rpPre s) : RpCtx s := by
  simp only [rpPre] at h
  sig_split h
  rename_i hsp hrd hwr dpq dpn dpe dpd dps dpa dqn dqe dqd dqs dqa dns des dds dsa dRp dRq dRn dRe
    dRd dRs dRa wP wQ wN wE wD wS hk hsi hcx hel1 hel2 hdl1 hdl2
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 4) ((stackArg s 5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 48⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hsi] at dpq dpn dpe dpd dps dpa dRp wP
  rw [hcx] at dpq dqn dqe dqd dqs dqa dRq wQ
  refine ⟨⟨hk1, hk2, hel1, hel2, hdl1, hdl2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, by simp only [rpIn]; omega_arith⟩, hsi, hcx, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 48) (by omega_arith) (by omega_arith))
      rw [← stkAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd]; simp) (by omega_arith) des,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi]; simp, contains_byte _ hj (by omega_arith)⟩,
      fun j hj => out_scr dps (contains_byte _ hj (by omega_arith))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hcx]; simp, contains_byte _ hj (by omega_arith)⟩,
      fun j hj => out_scr dqs (contains_byte _ hj (by omega_arith))⟩,
    apart_of dpq (by omega_arith) (by omega_arith), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega_arith) (by omega_arith)
  exact ⟨out_scr dRs hc, fun j hj he => dRp _ hc (by rw [he]; exact contains_byte _ hj (by omega_arith)),
    fun j hj he => dRq _ hc (by rw [he]; exact contains_byte _ hj (by omega_arith))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure RpHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 4) ((stackArg s 5).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 4
  rdx : t.gpr .rdx = s.gpr .r8
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .r9).toNat
  args : RpArgs t.mem (rpIn s).B (rpIn s).k (rpIn s).el (rpIn s).dl (rpIn s).pP (rpIn s).pQ (rpIn s).pN
    (rpIn s).pE (rpIn s).pD (rpIn s).sv
  inScr : InScr (stackArg s 4) ((stackArg s 5).toNat * 8) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem rpHead_ok' {s : State} (c : RpCtx s) :
    WP isa (.block (entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr))) s (RpHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .r9).toNat ≤ (stackArg s 5).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .r9).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 4) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (rpEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  have eN : Impl.Bignum.X86_64.Public.sN = 17 := rfl
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .r8 ∧
      t.gpr .rcx = s.gpr .r9 ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sN) (by omega_arith),
      hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega_arith), hN, hK]) rfl)
    fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hP hQ hN hK hE hEl hD hDl
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, ofNat_toNat64],
    ⟨hP, hQ, hN,
      show Bignum.word _ (stackArg s 4) _ = BitVec.ofNat 64 (s.gpr .r9).toNat by rw [hK, ofNat_toNat64],
      hE,
      show Bignum.word _ (stackArg s 4) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hEl, ofNat_toNat64],
      hD,
      show Bignum.word _ (stackArg s 4) _ = BitVec.ofNat 64 (stackArg s 3).toNat by rw [hDl, ofNat_toNat64],
      hsv⟩,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega_arith), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem rpPre_of {s t₁ t : State} (c : RpCtx s) (h : RpHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) : RpPre (rpIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 4) ((stackArg s 5).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.2.2, rdi := (k.gpr (by decide)).trans h.rdi, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oP := ⟨fun i hi => by rw [kk.2.2]; exact c.oP.wr i hi, c.oP.sep⟩,
      oQ := ⟨fun i hi => by rw [kk.2.2]; exact c.oQ.wr i hi, c.oQ.sep⟩,
      a := c.a, wr := kk.2.2, rsp := kk.gpr (by decide) }

/-- The saved registers and the return address, from what `fail` or `main`
leaves. -/
theorem rpGpr_of {s t₂ t : State} (c : RpCtx s) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (rpIn s).sv i)
    (hsp : t.gpr .rsp = t₂.gpr .rsp) (hsp₂ : t₂.gpr .rsp = s.gpr .rsp)
    (hfr : ∀ x, (stackArg s 5).toNat * 8 ≤ ofs (stackArg s 4) x →
      (∀ i < (s.gpr .r9).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 i) →
      (∀ i < (s.gpr .r9).toNat, x ≠ s.gpr .rdx + BitVec.ofNat 64 i) → t.mem x = s.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp.trans hsp₂
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZx, n1, n2⟩ := c.hret b hb
    exact hfr _ hZx n1 n2

end VG.Proof.Rsa.X86_64
