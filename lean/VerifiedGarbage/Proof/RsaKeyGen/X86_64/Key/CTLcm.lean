module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Res
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Res
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Algebra.GroupWithZero.Nat
meta import Mathlib.Tactic.Push
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! ### `RsaKeyGen.X86_64.Key.CTFront`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Key.Entry`, which only this module used -/

section

/-!
# An RSA key from its primes on x86-64: the entry and the head

`entry` saves the callee-saved registers and the arguments in the header,
with its base in `rdi` (`keyEntry_ok`); `head` sets up the working space
for `W = n_len / 8` words (`keyHead_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (kE kElen)

theorem keyEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 kNo) .rdi, .store (hdr11 kNl) .rsi, .store (hdr11 kDo) .rdx, .store (hdr11 kPp) .r8,
    .store (hdr11 kPl) .r9] : List Instr) ++
    (crtPairs [(0, kQp), (2, kDp), (4, kDq), (6, kQi), (8, kE), (9, kElen)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def keyEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl : BitVec 64) : Mem :=
  ((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * kNo)) vno).writeW
    (off B (8 * kNl)) vnl).writeW (off B (8 * kDo)) vdo).writeW (off B (8 * kPp)) vpp).writeW (off B (8 * kPl)) vpl

/-- The header after the entry's stores. -/
def keyEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) :
    Mem :=
  ((((((keyEntryMemA m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl).writeW (off B (8 * kQp)) vqp).writeW
    (off B (8 * kDp)) vdp).writeW (off B (8 * kDq)) vdq).writeW (off B (8 * kQi)) vqi).writeW
    (off B (8 * kE)) ve).writeW (off B (8 * kElen)) vel

theorem keyEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (keyEntryMemA m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl) := by
  unfold keyEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem keyEntryMem_facts (m : Mem) (B : Addr)
    (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) :
    let m' := keyEntryMem m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * kNo) = vno ∧ word m' B (8 * kNl) = vnl ∧
    word m' B (8 * kDo) = vdo ∧ word m' B (8 * kPp) = vpp ∧ word m' B (8 * kPl) = vpl ∧
    word m' B (8 * kQp) = vqp ∧ word m' B (8 * kDp) = vdp ∧ word m' B (8 * kDq) = vdq ∧
    word m' B (8 * kQi) = vqi ∧ word m' B (8 * kE) = ve ∧ word m' B (8 * kElen) = vel ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold m' keyEntryMem keyEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `entry` leaves. -/
structure KeyEntryPost (s t : State) (B : Addr) : Prop where
  rdi : t.gpr .rdi = B
  saved : ∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)
  no : word t.mem B (8 * kNo) = s.gpr .rdi
  nl : word t.mem B (8 * kNl) = s.gpr .rsi
  dd : word t.mem B (8 * kDo) = s.gpr .rdx
  pp : word t.mem B (8 * kPp) = s.gpr .r8
  pl : word t.mem B (8 * kPl) = s.gpr .r9
  qp : word t.mem B (8 * kQp) = stackArg s 0
  dp : word t.mem B (8 * kDp) = stackArg s 2
  dq : word t.mem B (8 * kDq) = stackArg s 4
  qi : word t.mem B (8 * kQi) = stackArg s 6
  e : word t.mem B (8 * kE) = stackArg s 8
  el : word t.mem B (8 * kElen) = stackArg s 9
  frame : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi] s t

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 10) in `rdi`. -/
theorem keyEntry_ok {s : State} {B : Addr} (hB : stackArg s 10 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 11, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s (KeyEntryPost s · B) := by
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = B := hB
  have ha10 := ha 10 (by decide)
  rw [keyEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = keyEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e10, ha10, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw kNo (by decide),
      hw kNl (by decide), hw kDo (by decide), hw kPp (by decide), hw kPl (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact keyEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = keyEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 2)
      (stackArg s 4) (stackArg s 6) (stackArg s 8) (stackArg s 9) := by
    rw [hm, hm₂, hm₁]; rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hNo, hNl, hDo, hPp, hPl, hQp, hDp, hDq, hQi, hE, hEl, ho⟩ :=
    keyEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 2)
      (stackArg s 4) (stackArg s 6) (stackArg s 8) (stackArg s 9)
  rw [← hmem] at h0 h1 h2 h3 h4 h5 hNo hNl hDo hPp hPl hQp hDp hDq hQi hE hEl ho
  refine ⟨hdi, fun i hi => ?_, hNo, hNl, hDo, hPp, hPl, hQp, hDp, hDq, hQi, hE, hEl, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ofNat_shr3 {k : Nat} (hk : k < 2 ^ 64) : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

/-- `head`: `W = n_len / 8`, the arrays' bases and the stride. -/
theorem keyHead_ok {s : State} {B : Addr} {Z nl : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hnl : word s.mem B (8 * kNl) = BitVec.ofNat 64 nl) (h16 : 16 ≤ nl) (hnl' : nl < 2 ^ 27)
    (hZ : slot (nl / 8) 16 ≤ Z) :
    WP isa (.block head) s fun t =>
      Ws t B Z (nl / 8) ∧ Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8)] s.mem t.mem ∧
        Keep [.rax, .rcx, .rdx, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot (nl / 8) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eN : kNl = 17 := rfl
  have hl8 : slot (nl / 8) 8 ≤ slot (nl / 8) 16 := by unfold slot; omega_arith
  unfold head
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (nl / 8) ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (nl / 8))) ?_ rfl)
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * kNl) (by omega_arith),
      hs.st (d := 8 * sW) (by omega_arith), hnl, ofNat_shr3 (show nl < 2 ^ 64 by omega_arith)]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega_arith))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (nl / 8) := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (nl / 8 + 2)))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, h12₂, hs₂.st (d := 8 * sStride) (by omega_arith), ofNat_dbl]
    congr 1
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ofNat_dbl, ofNat_dbl, ofNat_dbl]
    congr 1; omega_arith) rfl) fun t ⟨hm, k₃⟩ => ?_
  have o1 := writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (nl / 8 + 2))) (d := 8 * sStride) (by omega_arith)
  have hw : ∀ i < 32, i ≠ sStride → word t.mem B (8 * i) = word t₂.mem B (8 * i) :=
    fun i hi h1 => by rw [hm, o1.word (by omega_arith) (by omega_arith)]
  have kk := ((k₁.trans k₂).trans k₃)
  refine ⟨⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, ?_, ?_, fun j hj => ?_, hZ, by omega_arith,
    by omega_arith⟩, ?_, kk.mono (by simp)⟩
  · rw [hw sW (by decide) (by decide), ho₂.word (by omega_arith) (by omega_arith), hm₁, word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega_arith) (by unfold sArr sStride sFn; omega_arith)]
    exact hb₂ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    dsimp only at a b c
    rw [hm, o1 x c, ho₂ x b, hm₁, writeW_outside s.mem B _ (by omega_arith) x a]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

/-! ## Code -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: correctness

`code`, from a state `keyCtr` allows, ends as `keyOp` (`keyCode_wp`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

theorem code_eq : code = seqs (([.block (entry ++ head)] : List (Prog isa)) ++
    (((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask)))))) ++
    ([.ite .ne (zeros 2) keyPart] : List (Prog isa)))) := by
  simp only [code, List.append_assoc]

/-- The working space set up: `KS` from the state on entry, after `entry`
and `head`. -/
theorem keyStart_k {s : State} (c : KCtx s) :
    WP isa (.block (entry ++ head)) s fun t => KS (keyIn s) s.mem t := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ26 := c.hZ
  have hZ : slot (keyIn s).W 16 ≤ (arg s 11).toNat * 8 := Nat.le_trans (by unfold slot; omega_arith) hZ26
  have L := c.L
  have hpl : (keyIn s).pl = (s.gpr .r9).toNat := rfl
  have hpl1 := L.pl1
  have hpl2 := L.pl2
  have h256 : 8 * 32 ≤ (arg s 11).toNat * 8 := by
    have : 8 * 32 ≤ slot (keyIn s).W 16 := by unfold slot hdrBytes; omega_arith
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (keyEntry_ok rfl (fun i hi => hs.st (by omega_arith)) c.ha c.hsep) fun t₁ he => ?_
  have hs₁ := hs.congr he.keep.2.2
  have hnl : word t₁.mem (arg s 10) (8 * kNl) = BitVec.ofNat 64 (2 * (s.gpr .r9).toNat) := by
    rw [he.nl]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, c.rsi]; omega_arith)
  refine WP.mono (keyHead_ok hs₁ he.rdi hnl (by omega_arith) (by omega_arith) hZ) fun t₂ ⟨hw₂, hf₂, k₂⟩ => ?_
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have hi₁ : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₁.mem := InScr.of_outside he.frame (by omega_arith)
  have hi₂ : InScr (arg s 10) ((arg s 11).toNat * 8) t₁.mem t₂.mem := InScr.of_frm hf₂ (by
    have : 8 * sStride + 8 ≤ slot (keyIn s).W 16 := by rw [eS]; unfold slot hdrBytes; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
  have hi := hi₁.trans hi₂
  have hrd : t₂.rd = s.rd := k₂.2.1.trans he.keep.2.1
  have hwr : t₂.wr = s.wr := k₂.2.2.trans he.keep.2.2
  have hA₁ : KArgs t₁.mem (keyIn s) :=
    ⟨he.no, hnl, he.dd, he.pp, he.pl.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.qp, he.dp, he.dq, he.qi, he.e,
      he.el.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.saved⟩
  refine ⟨hw₂, hA₁.congr fun i hi' => hf₂.word_eq (fun r hr => ?_) (by omega_arith), c.p.congr hi hrd hwr,
    c.q.congr hi hrd hwr, c.e.congr hi hrd hwr, hi, hwr, ?_, hZ26,
    by simp only [keyIn, KIn.W]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · exact (k₂.gpr (by decide)).trans (he.keep.gpr (by decide))

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t₃ t : State} (c : KCtx s) (hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem)
    (R : OutsRes (keyIn s) t.mem (t.gpr .rax)) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (keyIn s).sv i)
    (hf : ∀ y, (keyIn s).Z ≤ ofs (keyIn s).B y →
      (∀ o ∈ outsL (keyIn s), ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = t₃.mem y)
    (hsp : t.gpr .rsp = (keyIn s).sp) :
    gprPreserved s t ∧ keyPost s t := by
  have ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.rsi]
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZb, hnb⟩ := c.hret b (by omega_arith)
    rw [hf _ hZb hnb, hi _ hZb]
  · unfold keyPost keyRes
    rw [ho]
    exact R

/-- `code` computes `keyOp`. -/
theorem keyCode_wp [InvLaw] (s : State) (h : keyPre s) : WP isa code s fun t => gprPreserved s t ∧ keyPost s t := by
  have c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (front_k k₁ c.L) fun t₃ ⟨F, hi₃⟩ => ?_)
  obtain ⟨ok, hok, hiff, hzf⟩ := F.zf
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  have hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem := k₁.inScr.trans hi₃
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok') (by simp [eval, hzf])
    (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    have hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      keyPost_of c hi (outsRes_zeros hd hsm Z) Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    have R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, hsv, hf, hsp⟩ := T
    exact keyPost_of c hi R hsv hf hsp

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTBase -/
section

/-!
# An RSA key from its primes on x86-64: constant time, the relation

Two runs agree on the public data (`KP`: the working space, the pointers
and lengths, `e` and the status). Between the pieces of the code, each run
is in a state `KS` describes for its own inputs, with the facts `F` the next
piece needs (`KG F`). A piece reloads `w` and the stride from the header
(`ws`) and computes the arrays' bases from them; the taint analysis checks
the rest of it from `rdi`, `r12` and `r9`, which correctness pins (`kg_ws`,
from `ws_ct`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The public part of the inputs. -/
structure KQ where
  B : Addr
  Z : Nat
  pl : Nat
  pN : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pE : Addr
  el : Nat
  eb : List Byte
  Wr : List Region
  sp : Addr

/-- The public data: the public inputs and the status. -/
structure KP where
  q : KQ
  st : Nat

def KIn.pub (I : KIn) : KQ := ⟨I.B, I.Z, I.pl, I.pN, I.pD, I.pP, I.pQ, I.pDp, I.pDq, I.pQi, I.pE, I.el, I.eb, I.Wr, I.sp⟩

/-- The status of the inputs. -/
abbrev KIn.st (I : KIn) : Nat := Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb)

/-- Between the pieces: the state of some inputs with the public data `p`,
with the facts `F`. -/
def KG (F : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I m₀, I.pub = p.q ∧ I.st = p.st ∧ KS I m₀ s ∧ KLens I ∧ KOuts I ∧ F I s

/-- No facts. -/
abbrev NF : KIn → State → Prop := fun _ _ => True

theorem KG.ws {F : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) :
    Ws s p.q.B p.q.Z (2 * p.q.pl / 8) := by
  obtain ⟨I, m₀, he, -, hk, -⟩ := h
  rw [← he]; exact hk.ws

theorem pins_kg (F : KIn → State → Prop) : Pins (KG F) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- `KG` with other facts. -/
theorem KG.imp {F G : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) (hFG : ∀ I, F I s → G I s) :
    KG G p s := by
  obtain ⟨I, m₀, he, hst, hk, L, O, hF⟩ := h
  exact ⟨I, m₀, he, hst, hk, L, O, hFG I hF⟩

/-- A piece from `KG F` to `KG G`, by what correctness gives from `KS`. -/
theorem kg_post {F G : KIn → State → Prop} {c : Prog isa}
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa c s fun t => KS I m₀ t ∧ G I t) :
    ∀ p s, KG F p s → WP isa c s (KG G p) := fun _ _ ⟨I, m₀, he, hst, hk, L, O, hF⟩ =>
  WP.mono (hw I m₀ _ hk L hF) fun _ ⟨hk', hG⟩ => ⟨I, m₀, he, hst, hk', L, O, hG⟩

/-- `ws` and then code the taint analysis checks from `rdi`, `r12` and
`r9`. -/
theorem kg_ws {F G : KIn → State → Prop} {rest : List Instr} {body : Prog isa}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s →
      WP isa (.seq (.block (ws ++ rest)) body) s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.seq (.block (ws ++ rest)) body) (Two (KG G)) :=
  ws_ct (fun p : KP => p.q.B) (fun p => p.q.Z) (fun p => 2 * p.q.pl / 8) (fun _ _ h => h.ws) ht (kg_post hw)

/-- `kg_ws` for a block. -/
theorem kg_wsb {F G : KIn → State → Prop} {rest : List Instr} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa (.block (ws ++ rest)) s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block (ws ++ rest)) (Two (KG G)) :=
  ws_block_ct (fun p : KP => p.q.B) (fun p => p.q.Z) (fun p => 2 * p.q.pl / 8) (fun _ _ h => h.ws) ht (kg_post hw)

/-- Code the taint analysis checks from `rdi` alone. -/
theorem kg_rdi {F G : KIn → State → Prop} {c : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) c hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa c s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) c (Two (KG G)) :=
  two_piece [.rdi] (pins_kg F) ht (kg_post hw)

/-- A sequence in two parts, each constant time. -/
theorem rs_app {P R Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h₁ : RelCT isa P (seqs a) R) (h₂ : RelCT isa R (seqs b) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  RelCT.seqs_app ha hb (RelCT.seq h₁ h₂)

/-- Facts that survive a piece which changes the parts `cs` and keeps the
registers outside `rs`. -/
def Stab (F : KIn → State → Prop) (cs : List Rc) (rs : List Reg) : Prop :=
  ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → KF I.B I.W cs s.mem t.mem → Keep rs s t → F I t

theorem kf_eq {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (hm : m' = m) : KF B W cs m m' := by
  rw [hm]; exact (KF.refl _ _ _).mono (by simp)

theorem stab_nf (cs : List Rc) (rs : List Reg) : Stab NF cs rs := fun _ _ _ _ _ _ _ => trivial

theorem Stab.mono {F : KIn → State → Prop} {cs cs' : List Rc} {rs rs' : List Reg} (h : Stab F cs rs)
    (hc : ∀ c ∈ cs', c ∈ cs) (hr : ∀ r ∈ rs', r ∈ rs) : Stab F cs' rs' :=
  fun I s t hZ hF hf k => h I s t hZ hF (hf.mono hc) ⟨fun r hr' => k.1 r fun h => hr' (hr r h), k.2⟩

/-- `e`'s value in its header slot. -/
abbrev EvOK : KIn → State → Prop := fun I t => word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E

theorem stab_ev {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kEv ∉ cs) :
    Stab EvOK cs rs := fun _ _ _ _ hF hf _ => (hf.word hok (by decide) hn).trans hF

theorem stab_and {F G : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (hF : Stab F cs rs)
    (hG : Stab G cs rs) : Stab (fun I t => F I t ∧ G I t) cs rs :=
  fun I s t hZ ⟨a, b⟩ hf k => ⟨hF I s t hZ a hf k, hG I s t hZ b hf k⟩

/-- The registers a piece may change: all but `rdi` and `rsp`. -/
abbrev allR : List Reg := [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem Stab.sub {F : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (h : Stab F cs allR)
    (hr : ∀ r ∈ rs, r ∈ allR := by decide) : Stab F cs rs :=
  h.mono (fun _ h => h) hr

theorem stab_r15 {cs : List Rc} {rs : List Reg} (h : .r15 ∉ rs) :
    Stab (fun _ t => ∃ c, t.gpr .r15 = mask c) cs rs := fun _ _ _ _ ⟨c, hc⟩ _ k => ⟨c, (k.gpr h).trans hc⟩

theorem stab_rbp {cs : List Rc} {rs : List Reg} (h : .rbp ∉ rs) :
    Stab (fun _ t => ∃ c, t.gpr .rbp = mask c) cs rs := fun _ _ _ _ ⟨c, hc⟩ _ k => ⟨c, (k.gpr h).trans hc⟩

/-- `KS` after a piece that changes no memory. -/
theorem KS.same {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hr : .rdi ∉ rs ∧ .rsp ∉ rs) : KS I m₀ t :=
  h.step (cs := []) (by rw [hm]; exact KF.refl _ _ _) rfl k hr

/-- A block of the registers alone, checked by the taint analysis from `rdi`. -/
theorem kg_regs {F G : KIn → State → Prop} {l : List Instr} {rs : List Reg} (hr : .rdi ∉ rs ∧ .rsp ∉ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (ht : (taint.check (Taint.ofRegs [.rdi]) (.block l) hc).isSome = true)
    (hw : ∀ I s, slot I.W 16 ≤ 2 ^ 64 → F I s → WP isa (.block l) s fun t => t.mem = s.mem ∧ Keep rs s t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block l) (Two (KG G)) :=
  kg_rdi ht fun I _ s h _ hf => WP.mono (hw I s h.hZ hf) fun _ ⟨hm, k, hg⟩ => ⟨h.same hm k hr, hg⟩

/-! ## The pieces of the key routines -/

theorem zeroA_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16)
    (hF : Stab F [.arr j] [.r12, .r9, .r8, .rax, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (KG F)) (zeroA j) (Two (KG F)) :=
  kg_ws ht fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun _ ⟨ht, f, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

theorem copyA_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] [.r12, .r9, .rsi, .rbx, .rax, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx)) Impl.Rsa.X86_64.copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (copyA o a) (Two (KG F)) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← e]
    exact WP.mono (copyA_k h ho ha hoa) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTUnits -/
section

/-!
# An RSA key from its primes on x86-64: constant time, the key routines

Each of `constA`, `ltA`, `eqMask`, `selC`, `subC`, `setOneA`, `divmod` and
`inverse` leaks the same from two runs in `KG F` and leaves `KG F`, for
facts `F` its changes keep (`Stab`); `selC`, `subC`, `setOneA` and
`inverse` need the facts their correctness needs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `constA`'s store of `x`. -/
theorem constBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (x : BitVec 32) :
    WP isa (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) s
      fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h.ws.scr.congr (k₂.trans k₃).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC)) (x.setWidth 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.st (d := slot I.W aC) (by omega_arith), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega_arith)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega_arith)
  have kk := (k₂.trans k₃).trans k₄
  exact ⟨h.step f₄ (all_mut_arr (by decide)) kk (by decide), f₄, kk.mono (by simp)⟩

theorem constA_ct {F : KIn → State → Prop} (x : BitVec 32) (hF : Stab F [.arr aC] [.r12, .r9, .r8, .rax, .r14, .rbx])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (constA x)) (Two (KG F)) := by
  have e : seqs (constA x) = .seq (zeroA aC)
      (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) := by
    simp only [constA, seqs, List.append_assoc]
  rw [e]
  exact RelCT.seq (zeroA_ct (by decide) (hF.mono (by simp) (by simp)) ht₁)
    (kg_wsb ht₂ fun I _ s h _ hf => WP.mono (constBlk_k h x) fun _ ⟨ht, f, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp))⟩)

theorem ltA_eq (a b : Nat) : seqs (ltA a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]) := by
  simp only [ltA, seqs, List.append_assoc]

theorem ltA_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a < av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))
      (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (ltA a b)) (Two (KG G)) := by
  rw [ltA_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← ltA_eq]
    exact WP.mono (ltA_k h ha hb) fun _ ⟨ht, hm, hbp, _, _, _, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

theorem eqMask_eq (a b : Nat) : seqs (eqMask a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr))))) (.seq (wordLoop 0 xorBody) (.block isZero)) := by
  simp only [eqMask, eqA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem eqMask_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (eqMask a b)) (Two (KG G)) := by
  rw [eqMask_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← eqMask_eq]
    exact WP.mono (eqMask_k h ha hb) fun _ ⟨ht, hm, hbp, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

/-- A mask in `rbp`. -/
abbrev RbpM : KIn → State → Prop := fun _ t => ∃ c, t.gpr .rbp = mask c

/-- A mask in `r15`. -/
abbrev R15M : KIn → State → Prop := fun _ t => ∃ c, t.gpr .r15 = mask c

theorem selC_eq (j : Nat) : seqs (selC j) = .seq (.block (ws ++ (base j .r8 ++ base aC .rsi))) (wordLoop 0 selBody) := by
  simp only [selC, seqs, List.append_assoc]

theorem selC_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    (hF : Stab F [.arr j] [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base aC .rsi))
      (wordLoop 0 selBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ RbpM I t)) (seqs (selC j)) (Two (KG F)) := by
  rw [selC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, hbp⟩ => by
    rw [← selC_eq]
    exact WP.mono (selC_k h hj hjC hbp) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

theorem subC_eq (o a : Nat) : seqs (subC o a) = .seq (.block (ws ++ (base a .r8 ++ (base aC .r10 ++ (base o .rsi ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subMBody) := by
  simp only [subC, seqs, List.append_assoc]

theorem subC_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoC : o ≠ aC) (haC : a ≠ aC)
    (hoa : o = a ∨ o ≠ a) (hF : Stab F [.arr o] [.r12, .r9, .r8, .r10, .rsi, .rbp, .rax, .rdx, .r14])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ R15M I t)) (seqs (subC o a)) (Two (KG F)) := by
  rw [subC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, h15⟩ => by
    rw [← subC_eq]
    exact WP.mono (subC_k h ho ha hoC haC hoa h15) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- Array `j` zero. -/
abbrev Zero (j : Nat) : KIn → State → Prop := fun I t => wv t.mem I.B (slot I.W j) (I.W + 2) = 0

theorem setOneA_eq (j : Nat) : setOneA j = ws ++ (base j .rbx ++
    ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
  simp only [setOneA, List.append_assoc]

theorem setOne_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .rbx, .rax])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ Zero j I t)) (.block (setOneA j)) (Two (KG F)) := by
  rw [setOneA_eq]
  exact kg_wsb ht fun I _ s h _ ⟨hf, hz⟩ => by
    rw [← setOneA_eq]
    exact WP.mono (setOne_k h hj hz) fun _ ⟨ht, f, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- `zeroA j` then `setOneA j`. -/
theorem one_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .r8, .rbx, .rax, .r14])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA j) (.block (setOneA j))) (Two (KG F)) :=
  RelCT.seq (kg_ws ht₁ fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun _ ⟨ht, f, hz, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp)), hz⟩)
    (setOne_ct hj (hF.mono (by simp) (by simp)) ht₂)

/-- The registers `divmod` and `inverse` may change. -/
abbrev dvRegs : List Reg := List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)

theorem divmod_eq (iQ iR iD iT : Nat) : divmod iQ iR iD iT = .seq (.block (ws ++ (base iR .r8 ++
    (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    ([.mov32 .r13 (.imm 0)] : List Instr))))))
    (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne)) := by
  simp only [divmod, divInit, seqs, List.append_assoc]

theorem divmod_ct {F : KIn → State → Prop} {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16)
    (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hF : Stab F [.arr iQ, .arr iR, .arr iT] dvRegs) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base iR .r8 ++
      (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
      ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (divmod iQ iR iD iT) (Two (KG F)) := by
  rw [divmod_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← divmod_eq]
    refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega_arith) h.ws.w2 h.ws.hZ hQ hR hD
      hT dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf', k, _⟩ => ?_
    have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf'
    have k' : Keep dvRegs s t :=
      ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
        ⟨hm, by simp [e]⟩), k.2⟩
    exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), hF I s t h.hZ hf f k'⟩

theorem inverse_eq (iU iV iX₂ iM : Nat) : inverse iU iV iX₂ iM =
    .seq (.block (ws ++ ([.mov .r13 (.reg .r12)] : List Instr))) (inverseN iU iV iX₂ iM) := rfl

theorem inverse_ct [InvLaw] {F : KIn → State → Prop} {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂)
    (hF : Stab F [.arr iV, .arr iX₂, .priv] allR)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ([.mov .r13 (.reg .r12)] : List Instr))
      (inverseN iU iV iX₂ iM)) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverse iU iV iX₂ iM) (Two (KG F)) := by
  rw [inverse_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← inverse_eq]
    exact WP.mono (inverse_k h hU hV hX₂ hM dVX₂) fun t ⟨ht, f, k, _⟩ => ⟨ht, hF I s t h.hZ hf f (k.mono (by decide))⟩

/-- `inverseK k`: the inverse at the width `n I` that `k` sets from `w`. -/
theorem inverseK_ct [InvLaw] {F : KIn → State → Prop} {k : List Instr} {n : KIn → Nat}
    (hk : ∀ (I : KIn) (t : State), t.gpr .r12 = BitVec.ofNat 64 I.W → I.W < 2 ^ 20 → WP isa (.block k) t fun t' =>
      t'.gpr .r13 = BitVec.ofNat 64 (n I) ∧ t'.mem = t.mem ∧ Keep [.r13] t t')
    (hn1 : ∀ I, KLens I → 1 ≤ n I) (hnw : ∀ I, KLens I → n I ≤ I.W) {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂)
    (hF : Stab F [.arr iV, .arr iX₂, .priv] allR)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block k) (inverseN iU iV iX₂ iM)) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverseK k iU iV iX₂ iM) (Two (KG F)) :=
  kg_ws ht fun I _ s h L hf =>
    WP.mono (inverseK_k h (hk I) (hn1 I L) (hnw I L) hU hV hX₂ hM dVX₂) fun t ⟨ht, f, k, _⟩ =>
      ⟨ht, hF I s t h.hZ hf f (k.mono (by decide))⟩

/-- `inverseK kHalf`: at the primes' width `w / 2`. -/
theorem inverseHalf_ct [InvLaw] {F : KIn → State → Prop} {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂)
    (hF : Stab F [.arr iV, .arr iX₂, .priv] allR)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block kHalf) (inverseN iU iV iX₂ iM)) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverseK kHalf iU iV iX₂ iM) (Two (KG F)) :=
  inverseK_ct (n := fun I => I.W / 2) (fun _ _ h12 hw => kHalf_ok h12 (by omega_using [hw]))
    (fun I L => by have := L.pl1; dsimp only [KIn.W]; omega_using [this]) (fun _ _ => Nat.div_le_self _ _) hU hV hX₂ hM dVX₂ hF ht

/-- `inverseK kOne`: at one word. -/
theorem inverseOne_ct [InvLaw] {F : KIn → State → Prop} {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂)
    (hF : Stab F [.arr iV, .arr iX₂, .priv] allR)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block kOne) (inverseN iU iV iX₂ iM)) hc).isSome = true) :
    RelCT isa (Two (KG F)) (inverseK kOne iU iV iX₂ iM) (Two (KG F)) :=
  inverseK_ct (n := fun _ => 1) (fun _ _ _ _ => kOne_ok) (fun _ _ => Nat.le_refl _)
    (fun I L => by have := L.pl1; dsimp only [KIn.W]; omega_using [this]) hU hV hX₂ hM dVX₂ hF ht

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTFront -/
section

/-!
# An RSA key from its primes on x86-64: constant time, the loads, the order and `p − 1`, `q − 1`

The loads take the pointer and the length from the header, which correctness
pins to the public data (`loadA_ct`, `loadE_ct`); the rest are pieces of
the key routines.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

/-- `loadA`'s block and `loadBE`, from `KS`. -/
theorem loadTail_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j sPtr sLen len : Nat} {ptr : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem I.B (8 * sPtr) = ptr)
    (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len) (hsrc : Src s I.B I.Z ptr bs) (hbl : bs.length = len)
    (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W) :
    WP isa (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] :
      List Instr))) loadBE) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧ Keep allR s t := by
  have hw := h.ws
  have hn := hw.scr.nowrap
  have sj := hw.sl hj
  have hw2 := hw.w2
  refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
  have ht := h.same hm k (by decide)
  have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega_arith) rfl (by omega_arith)
    (fun i hi => hsrc'.rd i (by omega_arith)) (fun i hi => hsrc'.val i (by omega_arith))
    (fun i hi => Or.inr (by have := hsrc'.out i (by omega_arith); omega_arith))) fun t' ⟨_, o, k'⟩ => ?_
  rw [hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega_arith)
  exact ⟨h.step f (all_mut_arr hj) (k.trans k') (by decide), f, (k.trans k').mono (by decide)⟩

theorem loadA_eq (j sPtr sLen : Nat) : seqs (loadA j sPtr sLen) = .seq (zeroA j)
    (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)))
      loadBE) := by
  simp only [loadA, seqs]

/-- `loadA j sPtr sLen` for the number whose pointer and length (functions of
the public inputs) are in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct {F : KIn → State → Prop} {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : ∀ I m₀ s, KS I m₀ s → KLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ 8 * I.W)
    (hF : Stab F [.arr j] allR) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rdi, .rbx, .rsi, .rcx]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (loadA j sPtr sLen)) (Two (KG F)) := by
  rw [loadA_eq]
  refine RelCT.seq (zeroA_ct hj (hF.mono (fun _ h => h) (by decide)) ht₁) ?_
  refine pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot (2 * p.q.pl / 8) j)) (ptr p.q) (len p.q)) (pins_kg F) ht₂ ?_ ht₃ ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hp, hl, -⟩ := hA I m₀ s hk L
    exact WP.mono (loadBlk_ok hk.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdi
      · exact hbx
      · exact hsi
      · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, hf⟩
    obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA I m₀ s hk L
    exact WP.mono (loadTail_k hk hj hP hL hp hl hsrc hbl hl1 hlw) fun t ⟨ht, f, k⟩ =>
      ⟨I, m₀, rfl, rfl, ht, L, O, hF I s t hk.hZ hf f k⟩

theorem loadAP_ct : RelCT isa (Two (KG NF)) (seqs (loadA aPa kPp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pP KQ.pl
    (fun I _ _ h L => ⟨h.args.pp, h.args.pl, ⟨_, h.p, L.pbl⟩, show 1 ≤ I.pl by have := L.pl1; omega_arith,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega_arith⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

theorem loadAQ_ct : RelCT isa (Two (KG NF)) (seqs (loadA aQa kQp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pQ KQ.pl
    (fun I _ _ h L => ⟨h.args.qp, h.args.pl, ⟨_, h.q, L.qbl⟩, show 1 ≤ I.pl by have := L.pl1; omega_arith,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega_arith⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

/-- `e`'s pointer and length. -/
def eVal (pE : Addr) (el : Nat) : Reg → BitVec 64
  | .rsi => pE
  | .rcx => BitVec.ofNat 64 el
  | _ => 0

theorem loadE_eq : seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))) =
    .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)), .mov32 .rbx (.imm 0)])
      (.seq (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) (.block [.store (hdr kEv) .rbx])) := rfl

/-- `e`'s load and its store into `kEv`. -/
theorem loadE_ct : RelCT isa (Two (KG NF)) (seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa)))) (Two (KG EvOK)) := by
  rw [loadE_eq]
  refine pin_ct [.rdi] [.rdi, .rsi, .rcx]
    (fun p : KP => fun r => if r = .rdi then p.q.B else eVal p.q.pE p.q.el r) (pins_kg NF) (by taint_decide) ?_
    (by taint_decide) ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
      hk.ws.scr.ld (by have := hk.ws.h256; omega_arith)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = I.pE ∧
        t.gpr .rcx = BitVec.ofNat 64 I.el) (by
      xrun [State.ea, hdr, hk.ws.rdi, hdrOff, hl kE (by decide), hl kElen (by decide), hk.args.e, hk.args.el]) rfl)
      fun t ⟨⟨hsi, hcx⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans hk.ws.rdi
    · exact hsi
    · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hg, hZ8⟩ := hk.ws.good
    have e₁ := loadE_ok hg hZ8 hk.args.e (by rw [hk.args.el, L.ebl]) (by rw [L.ebl]; exact L.el1)
      (by rw [L.ebl]; exact L.el8) hk.e
    rw [show seqs loadE = .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)),
      .mov32 .rbx (.imm 0)]) (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) from rfl] at e₁
    refine WP.assoc (WP.seq (WP.mono e₁ fun s₃ ⟨hbx, m₃, k₃⟩ => ?_))
    have h₃ := hk.same m₃ k₃ (by decide)
    have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega_arith)
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
      (BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb))) (by
        have hbx' : s₃.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
          rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hst, hbx']) rfl) fun t ⟨hm, k₄⟩ => ?_
    obtain ⟨ht, -, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega_arith) hm k₄ (by decide)
    exact ⟨I, m₀, rfl, rfl, ht, L, O, hw⟩

theorem order_eq : seqs order = .seq (.block (ws ++ (base aPa .rbx ++ (base aQa .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp])
      (.seq (.block [.mov .r15 (.reg .rbp)]) (wordLoop 0 cswapBody))) := by
  simp only [order, ltA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem order_ct : RelCT isa (Two (KG EvOK)) (seqs order) (Two (KG EvOK)) := by
  rw [order_eq]
  exact kg_ws (by taint_decide) fun I _ s h _ hf => by
    rw [← order_eq]
    exact WP.mono (order_k h) fun _ ⟨ht, f, _, _⟩ => ⟨ht, (f.word (by decide) (by decide) (by decide)).trans hf⟩

/-- `rbp`'s mask, negated, into `r15`. -/
theorem negR15_ok {s : State} {c : Bool} (h : s.gpr .rbp = mask c) :
    WP isa (.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.mem = s.mem ∧ Keep [.r15] s t ∧ t.gpr .r15 = mask (!c) := by
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!c) ∧ t.mem = s.mem)
    (by xrun [h, sxM1, maskNot]) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨hm, k, h15⟩

theorem decTo_eq (o j : Nat) : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (eqMask j aC ++
    (([.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 1 ++ subC o o)))) := by
  simp only [decTo, subC, List.append_assoc]

/-- `decTo o j`, for facts that its changes keep. -/
theorem decTo_ct {F : KIn → State → Prop} {o j : Nat} (ho : o < 16) (hj : j < 16) (hoj : o ≠ j) (hoC : o ≠ aC)
    (hF : Stab F [.arr o, .arr aC] allR)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 0), .store (at0 .rbx) .rax] : List Instr))) h₄).isSome = true)
    (t₅ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (base aC .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) h₅).isSome = true)
    (t₆ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) h₆).isSome = true)
    (t₇ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) h₇).isSome = true)
    (t₈ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) h₈).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (decTo o j)) (Two (KG F)) := by
  rw [decTo_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from
    RelCT.seq (zeroA_ct ho (hF.mono (by simp) (by decide)) t₁) (copyA_ct ho hj hoj (hF.mono (by simp) (by decide)) t₂)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (hF.mono (by simp) (by decide)) t₃ t₄) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := fun I t => F I t ∧ RbpM I t) hj
    (by decide) (fun I s t hZ hf hm k hbp => ⟨hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp))
      (k.mono (by decide)), _, hbp⟩) t₅) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]]) _ from
    kg_regs (G := fun I t => F I t ∧ R15M I t) (by decide) t₆ fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (negR15_ok hbp) fun t ⟨hm, k, h15⟩ =>
      ⟨hm, k, hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp)) (k.mono (by decide)), _, h15⟩) ?_
  refine rs_app (by simp [constA]) (by simp [subC]) (constA_ct 1
    (stab_and (hF.mono (by simp) (by decide)) (stab_r15 (by decide))) t₃ t₇) ?_
  exact subC_ct ho ho hoC hoC (.inl rfl) (hF.mono (by simp) (by decide)) t₈

theorem decP_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aPm aPa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

theorem decQ_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aQm aQa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-!
# An RSA key from its primes on x86-64: constant time, `lcm(p − 1, q − 1)`

The product (`mul_ct`), the copies of `p − 1` and `q − 1` (`zc_ct`, which
leave their top words zero, as `inverse` needs of `u`), the halving's loop
(`twos_ct`, by `RelCT.loop` over the steps left), `gcdUV` (`gcdUV_ct`) and
the division.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Word `W` of array `j` zero. -/
abbrev TopZ (j : Nat) : KIn → State → Prop := fun I t => atop I t.mem j = 0

theorem stab_top {j : Nat} {cs : List Rc} (rs : List Reg) (hj : j < 16) (hok : cs.all Rc.ok = true)
    (hn : .arr j ∉ cs) : Stab (TopZ j) cs rs := fun _ _ _ hZ h f _ => (f.top hok hj hn hZ).trans h

/-! ## The product -/

/-- The product's block: the bases of `a`, `b` and `o`, and `w = W / 2`. -/
abbrev mulBlk (a b o : Nat) : List Instr :=
  base a .r11 ++ (base b .rax ++ (base o .r8 ++ ([.mov .r9 (.reg .rax), .mov .r10 (.reg .r12), .shift .shr .r10 1,
    .alu .sub .r12 (.reg .r10)] : List Instr)))

/-- `[o] += [a] [b]` (`w` words each) from a zero `[o]`. -/
theorem mulTail_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) {a b o : Nat} (ha : a < 16)
    (hb : b < 16) (ho : o < 16) (hao : a ≠ o) (hbo : b ≠ o) (hz : Zero o I s) :
    WP isa (.seq (.block (ws ++ mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows) s fun t =>
      KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧ Keep allR s t := by
  have hW := L.W
  have hn := h.ws.scr.nowrap
  obtain sP := h.ws.sl ha
  obtain sQ := h.ws.sl hb
  obtain sL := h.ws.sl ho
  obtain p1 := slot_far (w := I.W) hao
  obtain p2 := slot_far (w := I.W) hbo
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  obtain hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok a (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok b (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok o (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  obtain h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  obtain hax₅ : s₅.gpr .rax = off I.B (slot I.W b) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W b) ∧
      t.gpr .r10 = BitVec.ofNat 64 (I.pl / 8) ∧ t.gpr .r12 = BitVec.ofNat 64 (I.pl / 8) ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega_arith)]
    refine ⟨by rw [hW]; congr 1; omega_arith, ?_⟩
    rw [ofNat_sub' (by omega_arith) (by omega_arith)]; congr 1; omega_arith) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  obtain k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  obtain hm₆ : s₆.mem = s.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  obtain hz₆ : wv s₆.mem I.B (slot I.W o) (I.pl / 8 + I.pl / 8 + 2) = 0 := by
    rw [hm₆, ← hz]; congr 1; omega_arith
  refine WP.mono (mulRows_ok (h.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨_, o', k₇⟩ => ?_
  rw [hm₆] at o'
  obtain f := KF.arr1 (I := I) (j := o) o' (Nat.le_refl _) (by omega_arith)
  exact ⟨h.step f (all_mut_arr ho) (k26.trans k₇) (by decide), f, (k26.trans k₇).mono (by decide)⟩

/-- `[o] := [a] [b]`, as `phi` and `nPart` compute it. -/
theorem mul_ct {F : KIn → State → Prop} {a b o : Nat} (ha : a < 16) (hb : b < 16) (ho : o < 16) (hao : a ≠ o)
    (hbo : b ≠ o) (hF : Stab F [.arr o] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows) hc₂).isSome =
      true) :
    RelCT isa (Two (KG F)) (.seq (zeroA o) (.seq (.block (ws ++ mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows)) (Two (KG F)) :=
  RelCT.seq (kg_ws (G := fun I t => F I t ∧ Zero o I t) ht₁ fun I _ s h _ hf =>
      WP.mono (zeroA_k h ho) fun _ ⟨ht, f, hz, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), hz⟩)
    (kg_ws ht₂ fun I _ s h L ⟨hf, hz⟩ => WP.mono (mulTail_k h L ha hb ho hao hbo hz) fun _ ⟨ht, f, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f k⟩)

theorem phi_eq : seqs phi = .seq (zeroA aL) (.seq (.block (ws ++ mulBlk aPm aQm aL)) Impl.Rsa.X86_64.Crt.mulRows) := by
  simp only [phi, seqs, mulBlk, List.append_assoc]

/-! ## The copies -/

/-- `[o] := [a]`, with word `W` of `[o]` zero. -/
theorem zc_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA o) (copyA o a)) (Two (KG fun I t => F I t ∧ TopZ o I t)) := by
  obtain e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  refine RelCT.seq (kg_ws (G := fun I t => F I t ∧ TopZ o I t) ht₁ fun I _ s h _ hf =>
    WP.mono (zeroA_k h ho) fun _ ⟨ht, f, hz, k⟩ => ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), (wv_zero2 hz).2⟩) ?_
  rw [e]
  exact kg_ws ht₂ fun I _ s h _ ⟨hf, ht0⟩ => by
    rw [← e]
    exact WP.mono (copyA_k h ho ha hoa) fun _ ⟨ht, f, _, tt, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), tt.trans ht0⟩

/-! ## The halving -/

/-- `halfIf j` changes array `j` (but its word `W`) and `aT`. -/
theorem halfIfF_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (hmo : word s.mem I.B (8 * sMo) = mask c) :
    WP isa (seqs (halfIf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      atop I t.mem j = atop I s.mem j ∧ Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  obtain sj := h.ws.sl hj
  obtain sT := h.ws.sl (j := aT) (by decide)
  obtain sp := slot_far (w := I.W) hjT
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨_, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at o₃
  obtain f₃ := KF.arr1 (I := I) (j := aT) o₃ (Nat.le_refl _) (by omega_arith)
  obtain h₃ := h.step f₃ (all_mut_arr (by decide)) ((k₁.trans k₂).trans k₃) (by decide)
  obtain hok : [Rc.arr aT].all Rc.ok = true := by decide
  obtain tj₃ : atop I s₃.mem j = atop I s.mem j := f₃.top hok hj (by simp [hjT]) hZ
  obtain hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok (by decide) (by decide), hmo]
  obtain k13 := (k₁.trans k₂).trans k₃
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧
      t.mem = s₃.mem) (by
    obtain hl := h₃.ws.scr.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_arith)
    xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hl, hmo₃, sxM1, maskNot]) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₄.gpr (by decide)).trans h₃.ws.rdi) ((k₄.gpr (by decide)).trans (((k₂.trans k₃).gpr (by decide)).trans h9))
      (by decide)) fun s₅ ⟨h8₅, hsi₅, m₅, k₅⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr ((k13.trans k₄).trans k₅).2.2) h8₅ hsi₅ ((k₅.gpr (by decide)).trans hbp)
    (((k₄.trans k₅).gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨_, o, k₆⟩ => ?_
  rw [m₅, m₄] at o
  obtain f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega_arith)
  refine ⟨h₃.step f (all_mut_arr hj) ((k₄.trans k₅).trans k₆) (by decide), (f₃.trans f).mono (by simp), ?_,
    (((k13.trans k₄).trans k₅).trans k₆).mono (by decide)⟩
  dsimp only [atop]; rw [o.word (Or.inr (Nat.le_refl _)) (by omega_arith)]; exact tj₃

/-- The mask of `u` and `v` both even, into `sMo`. -/
abbrev twoBlk : List Instr := base aU .rbx ++ (base aV .r10 ++ ([.mov .rax (.mem (at0 .rbx)),
  .alu .or .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1), .store (hdr sMo) .rax] :
  List Instr))

/-- A mask in `sMo`. -/
abbrev SmoM : KIn → State → Prop := fun I t => ∃ c, word t.mem I.B (8 * sMo) = mask c

theorem twoBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ twoBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr sMo] s.mem t.mem ∧ SmoM I t ∧
      Keep [.r12, .r9, .rbx, .r10, .rax] s t := by
  have hn := h.ws.scr.nowrap
  obtain sU := h.ws.sl (j := aU) (by decide)
  obtain sV := h.ws.sl (j := aV) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
  obtain hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₁ h9) fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
  obtain hs₃ := h.ws.scr.congr ((k₁.trans k₂).trans k₃).2.2
  obtain hbx₃ : s₃.gpr .rbx = off I.B (slot I.W aU) := (k₃.gpr (by decide)).trans hbx
  obtain hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
  obtain hm₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * sMo))
      (((s.mem.readW (off I.B (slot I.W aU)) 64 ||| s.mem.readW (off I.B (slot I.W aV)) 64) &&& 1) - 1)) (by
    xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := slot I.W aU) (by omega_arith), hs₃.ld (d := slot I.W aV) (by omega_arith),
      hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_arith), hm₃]) rfl) fun t ⟨hm, k₄⟩ => ?_
  rw [twoMask] at hm
  obtain kk := ((k₁.trans k₂).trans k₃).trans k₄
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := sMo) (by unfold sMo sFn; omega_arith) hm kk (by decide)
  exact ⟨ht, f, ⟨_, hw⟩, kk.mono (by decide)⟩

/-- The facts the halving keeps: `F`, and words `W` of `u` and `v` zero. -/
abbrev TwB (F : KIn → State → Prop) : KIn → State → Prop := fun I t => F I t ∧ TopZ aU I t ∧ TopZ aV I t

/-- Before a step of the halving, with `n` steps left. -/
abbrev TwF (F : KIn → State → Prop) (n : Nat) : KIn → State → Prop := fun I t => TwB F I t ∧
  t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 (64 * I.W - n) ∧ 0 < n ∧ n ≤ 64 * I.W

/-- After a step of the halving, from `n` steps left. -/
abbrev TwP (F : KIn → State → Prop) (n : Nat) : KIn → State → Prop := fun I t => TwB F I t ∧
  t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 (64 * I.W - n + 1) ∧
  t.zf = some (decide (64 * I.W - n + 1 = 64 * I.W)) ∧ 0 < n ∧ n ≤ 64 * I.W

theorem halfIf_eq (j : Nat) : seqs (halfIf j) = .seq (.block (ws ++ (base j .r8 ++ base aT .rsi)))
    (.seq (wordLoop 0 shrBody) (.seq (.block (([.mov .rbp (.mem (hdr sMo)),
      .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ (base j .r8 ++ base aT .rsi))) (wordLoop 0 selBody))) := by
  simp only [halfIf, seqs, List.append_assoc]

theorem halfIf_ct {F : KIn → State → Prop} {n j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR)
    (hjs : Rc.arr j ∈ [Rc.arr aU, Rc.arr aV, Rc.arr aL, Rc.arr aT, Rc.hdr sMo]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base aT .rsi))
      (.seq (wordLoop 0 shrBody) (.seq (.block (([.mov .rbp (.mem (hdr sMo)),
      .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ (base j .r8 ++ base aT .rsi))) (wordLoop 0 selBody)))) hc).isSome =
      true) :
    RelCT isa (Two (KG fun I t => TwF F n I t ∧ SmoM I t)) (seqs (halfIf j))
      (Two (KG fun I t => TwF F n I t ∧ SmoM I t)) := by
  rw [halfIf_eq]
  refine kg_ws ht fun I _ s h _ ⟨⟨⟨hf, tU, tV⟩, h11, h13, hn⟩, c, hmo⟩ => ?_
  rw [← halfIf_eq]
  refine WP.mono (halfIfF_k h hj hjT hmo) fun t ⟨ht, f, tj, k⟩ => ?_
  have hZ := h.hZ
  obtain hok : [Rc.arr j, Rc.arr aT].all Rc.ok = true := by
    simp only [List.all_cons, List.all_nil, Rc.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hj, by decide⟩
  obtain top : ∀ i < 16, i ≠ aT → atop I t.mem i = atop I s.mem i := fun i hi hiT =>
    if e : i = j then e ▸ tj else f.top hok hi (by simp [e, hiT]) hZ
  refine ⟨ht, ⟨⟨hF I s t hZ hf (f.mono fun c hc => ?_) (k.mono (by decide)), (top aU (by decide) (by decide)).trans tU,
    (top aV (by decide) (by decide)).trans tV⟩, (k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h13, hn⟩,
    c, (f.word hok (by decide) (by simp)).trans hmo⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact hjs
  · simp

theorem twoStep_eq : twoStep = seqs (([.block (ws ++ twoBlk)] : List (Prog isa)) ++ (halfIf aU ++ (halfIf aV ++ (halfIf aL ++
    ([.block countP] : List (Prog isa)))))) := by
  simp only [twoStep, twoBlk, List.append_assoc]

theorem twoStep_ct {F : KIn → State → Prop} (n : Nat) (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR) :
    RelCT isa (Two (KG (TwF F n))) twoStep (Two (KG (TwP F n))) := by
  rw [twoStep_eq]
  refine rs_app (by simp) (by simp [halfIf]) (show RelCT isa _ (seqs [.block (ws ++ twoBlk)]) _ from
    kg_wsb (G := fun I t => TwF F n I t ∧ SmoM I t) (by taint_decide)
      fun I _ s h _ ⟨⟨hf, tU, tV⟩, h11, h13, hn⟩ => WP.mono (twoBlk_k h) fun t ⟨ht, f, hmo, k⟩ => by
        obtain hok : [Rc.hdr sMo].all Rc.ok = true := by decide
        exact ⟨ht, ⟨⟨hF I s t h.hZ hf (f.mono (by decide)) (k.mono (by decide)),
          (f.top hok (by decide) (by decide) h.hZ).trans tU, (f.top hok (by decide) (by decide) h.hZ).trans tV⟩,
          (k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h13, hn⟩, hmo⟩) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide) hF (by simp)
    (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide) hF (by simp)
    (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp) (halfIf_ct (by decide) (by decide) hF (by simp) (by taint_decide)) ?_
  exact kg_regs (rs := [.r13]) (by decide) (by taint_decide) fun I s hZ ⟨⟨hb, h11, h13, hn⟩, _⟩ =>
    WP.mono (countP_ok s h13 h11 (by unfold slot hdrBytes at hZ; omega_arith) (by unfold slot hdrBytes at hZ; omega_arith))
      fun t ⟨hz, h13', hm, k⟩ => by
      obtain hb' : TwB F I t := by
        obtain ⟨hf, tU, tV⟩ := hb
        refine ⟨hF I s t hZ hf (by rw [hm]; exact (KF.refl _ _ _).mono (by decide)) (k.mono (by decide)), ?_, ?_⟩
        · dsimp only [TopZ, atop]; rw [hm]; exact tU
        · dsimp only [TopZ, atop]; rw [hm]; exact tV
      exact ⟨hm, k, hb', (k.gpr (by decide)).trans h11, h13', hz, hn⟩

theorem divInit_eq (iT : Nat) : divInit iT = ws ++ (base iT .r8 ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
    (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))) := by
  simp only [divInit, List.append_assoc]

theorem twos_ct {F : KIn → State → Prop} (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR) :
    RelCT isa (Two (KG (TwB F))) (seqs twos) (Two (KG (TwB F))) := by
  have e : seqs twos = .seq (.block (divInit aT)) (.loop twoStep .ne) := rfl
  rw [e, divInit_eq]
  refine RelCT.seq (kg_wsb (G := fun I t => TwB F I t ∧ t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧
      t.gpr .r13 = BitVec.ofNat 64 0) (by taint_decide) fun I _ s h _ ⟨hf, tU, tV⟩ => by
    rw [← divInit_eq]
    exact WP.mono (divInit_k h aT) fun t ⟨h11, h13, hm, k⟩ =>
      ⟨h.same hm k (by decide), ⟨hF I s t h.hZ hf (by rw [hm]; exact (KF.refl _ _ _).mono (by decide)) (k.mono (by decide)),
        by dsimp only [TopZ, atop]; rw [hm]; exact tU, by dsimp only [TopZ, atop]; rw [hm]; exact tV⟩, h11, h13⟩) ?_
  -- The loop, over the steps left.
  obtain hW : ∀ {G : KIn → State → Prop} {p : KP} {s : State}, KG G p s →
      ∃ I m₀, I.pub = p.q ∧ I.st = p.st ∧ KS I m₀ s ∧ KLens I ∧ KOuts I ∧ G I s ∧ I.W = 2 * p.q.pl / 8 :=
    fun ⟨I, m₀, he, hst, hk, L, O, hg⟩ => ⟨I, m₀, he, hst, hk, L, O, hg, by rw [← he]; rfl⟩
  refine RelCT.mono (RelCT.exists_ fun n => RelCT.loop (fun n => Two (KG (TwF F n))) (fun n => ?_) n)
    (fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨64 * (2 * p.q.pl / 8), p, ?_, ?_⟩) (fun _ _ h => h)
  rotate_left
  · obtain ⟨I, m₀, he, hst, hk, L, O, ⟨hb, h11, h13⟩, hIW⟩ := hW h₁
    have := hk.ws.w1
    exact ⟨I, m₀, he, hst, hk, L, O, hb, h11, by rw [hIW, Nat.sub_self]; exact h13, by rw [← hIW]; omega_arith,
      by rw [hIW]⟩
  · obtain ⟨I, m₀, he, hst, hk, L, O, ⟨hb, h11, h13⟩, hIW⟩ := hW h₂
    have := hk.ws.w1
    exact ⟨I, m₀, he, hst, hk, L, O, hb, h11, by rw [hIW, Nat.sub_self]; exact h13, by rw [← hIW]; omega_arith,
      by rw [hIW]⟩
  refine (twoStep_ct n hF).mono (fun _ _ h => h) fun s₁ s₂ ⟨p, h₁, h₂⟩ => ?_
  obtain ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, ⟨hb₁, h11₁, h13₁, hz₁, hn₁⟩, hW₁⟩ := hW h₁
  obtain ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, ⟨hb₂, h11₂, h13₂, hz₂, hn₂⟩, hW₂⟩ := hW h₂
  rw [hW₁] at h11₁ h13₁ hz₁ hn₁
  rw [hW₂] at h11₂ h13₂ hz₂ hn₂
  refine ⟨by simp only [eval, hz₁, hz₂], fun hf => ⟨p, ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, hb₁⟩,
    ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, hb₂⟩⟩, fun ht => ⟨n - 1, by omega_arith, p, ?_, ?_⟩⟩
  · simp only [eval, hz₁, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at ht
    refine ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, hb₁, by rw [hW₁]; exact h11₁, ?_, by omega_arith, by rw [hW₁]; omega_arith⟩
    rw [hW₁, h13₁]; congr 1; omega_arith
  · simp only [eval, hz₁, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at ht
    refine ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, hb₂, by rw [hW₂]; exact h11₂, ?_, by omega_arith, by rw [hW₂]; omega_arith⟩
    rw [hW₂, h13₂]; congr 1; omega_arith

/-! ## `gcd(u, v)` -/

/-- A mask in `kOk`. -/
abbrev KokM : KIn → State → Prop := fun I t => ∃ c, word t.mem I.B (8 * kOk) = mask c

theorem stab_kok {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kOk ∉ cs) :
    Stab KokM cs rs := fun _ _ _ _ ⟨c, h⟩ f _ => ⟨c, (f.word hok (by decide) hn).trans h⟩

/-- `rbp`'s mask into `kOk`, and `rbp` negated. -/
theorem kokPut_ok {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool} (hbp : s.gpr .rbp = mask c) :
    WP isa (.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧ word t.mem I.B (8 * kOk) = mask c ∧
      t.gpr .rbp = mask (!c) ∧ Keep [.rbp] s t := by
  obtain hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask c) ∧
    t.gpr .rbp = mask (!c)) (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun t ⟨⟨hm, hbp'⟩, k⟩ => ?_
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) hm k (by decide)
  exact ⟨ht, f, hw, hbp', k⟩

/-- `kOk`'s mask, negated, into `rbp`. -/
theorem kokGetNot_ok {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool}
    (hk : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.mem = s.mem ∧ Keep [.rbp] s t ∧ t.gpr .rbp = mask (!c) := by
  obtain hl := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hl, hk, sxM1, maskNot]) rfl) fun t ⟨⟨hbp, hm⟩, k⟩ => ⟨hm, k, hbp⟩

/-- `gcdUV`'s first block, after `ws`. -/
abbrev gcdBlk : List Instr :=
  base aV .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .mov .r15 (.reg .rax),
    .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++ (base aU .rbx ++ base aV .r10))

/-- `gcdUV`'s swap of `u` and `v`, which keeps word `W` of `u`. -/
theorem gcdSwap_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.seq (.block (ws ++ gcdBlk)) (wordLoop 0 cswapBody)) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aU, .arr aV] s.mem t.mem ∧ atop I t.mem aU = atop I s.mem aU ∧ Keep allR s t := by
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  obtain sU := h.ws.sl (j := aU) (by decide)
  obtain sV := h.ws.sl (j := aV) (by decide)
  obtain spUV := slot_far (w := I.W) (i := aU) (j := aV) (by decide)
  obtain e : ws ++ gcdBlk = oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      (base aU .rbx ++ base aV .r10) := by
    simp only [gcdBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  obtain hb : WP isa (.block (oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      (base aU .rbx ++ base aV .r10))) s fun t => t.mem = s.mem ∧ (∃ c, t.gpr .r15 = mask c) ∧
      t.gpr .rbx = off I.B (slot I.W aU) ∧ t.gpr .r10 = off I.B (slot I.W aV) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .r15, .r10] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aV) (by decide)) fun s₁ ⟨m₁, hax, h12, h9, k₁⟩ => ?_)
    refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask
      (!decide (av I s.mem aV % 2 = 1)) ∧ t.mem = s₁.mem) (by xrun [hax, sxM1, maskNot]) rfl)
      fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_)
    obtain hdi₂ : s₂.gpr .rdi = I.B := ((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi
    obtain h9₂ : s₂.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := (k₂.gpr (by decide)).trans h9
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₂ h9₂) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
      ((k₃.gpr (by decide)).trans h9₂)) fun t ⟨h10, m₄, k₄⟩ => ⟨by rw [m₄, m₃, m₂, m₁],
        ⟨_, ((k₃.trans k₄).gpr (by decide)).trans h15⟩, (k₄.gpr (by decide)).trans hbx, h10,
        (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h12, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨m₁, ⟨c, h15⟩, hbx, h10, h12, k₁⟩ => ?_)
  refine WP.mono (cswap_ok (h.ws.scr.congr k₁.2.2) hbx h10 h15 h12 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t ⟨_, _, hf, k₂⟩ => ?_
  rw [m₁] at hf
  obtain f₂ : KF I.B I.W [.arr aU, .arr aV] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
  refine ⟨h.step f₂ (all_mut_arrs (js := [aU, aV]) (by decide)) (k₁.trans k₂) (by decide), f₂, ?_,
    (k₁.trans k₂).mono (by decide)⟩
  dsimp only [atop]
  exact hf.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)

theorem gcdUV_eq2 : gcdUV = ([.block (ws ++ gcdBlk), wordLoop 0 cswapBody] : List (Prog isa)) ++ (constA 2 ++ (ltA aV aC ++
    (([.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 3 ++ (selC aV ++
    ([zeroA aM, copyA aM aV, inverseK kHalf aU aV aX₂ aM] ++
    (constA 1 ++ (([.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++
      selC aV)))))))) := by
  simp only [gcdUV, gcdBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]

/-- What `gcdUV` changes. -/
abbrev csG : List Rc := [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk, .priv]

theorem gcdUV_ct [InvLaw] {F : KIn → State → Prop} (hF : Stab F csG allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ TopZ aU I t)) (seqs gcdUV) (Two (KG F)) := by
  obtain sF : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → Stab F cs allR := fun _ hc => hF.mono hc (by simp)
  obtain sT : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs allR :=
    fun _ hok hn => stab_top _ (by decide) hok hn
  obtain sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs allR :=
    fun _ hok hn => stab_kok _ hok hn
  obtain sFT : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .arr aU ∉ cs →
      Stab (fun I t => F I t ∧ TopZ aU I t) cs allR := fun cs h1 h2 h3 => stab_and (sF cs h1) (sT cs h2 h3)
  obtain sFTK : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .arr aU ∉ cs → .hdr kOk ∉ cs →
      Stab (fun I t => (F I t ∧ TopZ aU I t) ∧ KokM I t) cs allR :=
    fun cs h1 h2 h3 h4 => stab_and (sFT cs h1 h2 h3) (sK cs h2 h4)
  obtain sFK : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => F I t ∧ KokM I t) cs allR := fun cs h1 h2 h4 => stab_and (sF cs h1) (sK cs h2 h4)
  rw [gcdUV_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block (ws ++ gcdBlk), wordLoop 0 cswapBody]) _
    from kg_ws (G := fun I t => F I t ∧ TopZ aU I t) (by taint_decide) fun I _ s h _ ⟨hf, tU⟩ =>
      WP.mono (gcdSwap_k h) fun t ⟨ht, f, tt, k⟩ => ⟨ht, sF _ (by simp) I s t h.hZ hf f k, tt.trans tU⟩) ?_
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 2 (sFT [.arr aC] (by simp) (by decide) (by decide)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := fun I t => (F I t ∧ TopZ aU I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨sFT [] (by simp) (by decide) (by decide) I s t hZ hf
      (kf_eq hm) (k.mono (by decide)), _, hbp⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.store (hdr kOk) .rbp,
    .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]]) _ from kg_rdi
    (G := fun I t => ((F I t ∧ TopZ aU I t) ∧ KokM I t) ∧ RbpM I t) (by taint_decide)
    fun I _ s h _ ⟨hf, c, hbp⟩ => WP.mono (kokPut_ok h hbp) fun t ⟨ht, f, hk, hbp', k⟩ =>
      ⟨ht, ⟨sFT [.hdr kOk] (by simp) (by decide) (by decide) I s t h.hZ hf f (k.mono (by decide)), _, hk⟩,
        _, hbp'⟩) ?_
  refine rs_app (by simp [constA]) (by simp [selC]) (constA_ct 3 (stab_and (sFTK [.arr aC] (by simp) (by decide)
    (by decide) (by decide)).sub (stab_rbp (by decide))) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [selC]) (by simp) (selC_ct (by decide) (by decide)
    (sFTK [.arr aV] (by simp) (by decide) (by decide) (by decide)).sub (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => F I t ∧ KokM I t)) (by simp) (by simp [constA]) ?_ ?_
  · -- `inverse` modulo `[aM] = v`.
    show RelCT isa _ (seqs ([zeroA aM] ++ ([copyA aM aV] ++ [inverseK kHalf aU aV aX₂ aM]))) _
    refine rs_app (by simp) (by simp) (zeroA_ct (by decide) (sFTK [.arr aM] (by simp) (by decide) (by decide)
      (by decide)).sub (by taint_decide)) ?_
    refine rs_app (by simp) (by simp) (copyA_ct (o := aM) (a := aV) (by decide) (by decide) (by decide)
      (sFTK [.arr aM] (by simp) (by decide) (by decide) (by decide)).sub (by taint_decide)) ?_
    refine (inverseHalf_ct (F := fun I t => F I t ∧ KokM I t) (by decide) (by decide) (by decide) (by decide)
      (by decide) (sFK _ (by simp) (by decide) (by decide)).sub (by taint_decide)).mono
      (fun s₁ s₂ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p, h₁.imp fun I ⟨⟨hf, _⟩, hk⟩ => ⟨hf, hk⟩,
        h₂.imp fun I ⟨⟨hf, _⟩, hk⟩ => ⟨hf, hk⟩⟩) h)
      fun _ _ h => h
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (sFK [.arr aC] (by simp) (by decide) (by decide)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [.mov .rbp (.mem (hdr kOk)),
    .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]]) _ from kg_rdi (G := fun I t => F I t ∧ RbpM I t)
    (by taint_decide) fun I _ s h _ ⟨hf, c, hk⟩ => WP.mono (kokGetNot_ok h hk) fun t ⟨hm, k, hbp⟩ =>
      ⟨h.same hm k (by decide), sF [] (by simp) I s t h.hZ hf (kf_eq hm) (k.mono (by decide)), _, hbp⟩) ?_
  exact selC_ct (by decide) (by decide) (sF [.arr aV] (by simp)).sub (by taint_decide)

theorem phi_ct : RelCT isa (Two (KG EvOK)) (seqs phi) (Two (KG EvOK)) := by
  rw [phi_eq]
  exact mul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)

/-- `lcmPart`, keeping `e` in `kEv`. -/
theorem lcmPart_ct [InvLaw] : RelCT isa (Two (KG EvOK)) (seqs lcmPart) (Two (KG EvOK)) := by
  obtain sE : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kEv ∉ cs → Stab EvOK cs allR :=
    fun _ hok hn => stab_ev _ hok hn
  rw [lcmPart_eq]
  refine rs_app (by simp [phi]) (by simp) phi_ct ?_
  refine rs_app (by simp) (by simp [twos]) (show RelCT isa _ (seqs ([zeroA aU, copyA aU aPm] ++
    [zeroA aV, copyA aV aQm])) (Two (KG (TwB EvOK))) from rs_app (by simp) (by simp)
      (zc_ct (by decide) (by decide) (by decide) (sE _ (by decide) (by decide)) (by taint_decide) (by taint_decide))
      ((zc_ct (by decide) (by decide) (by decide) (stab_and (sE [.arr aV] (by decide) (by decide))
        (stab_top _ (by decide) (by decide) (by decide))) (by taint_decide) (by taint_decide)).mono
        (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
          ⟨p, h₁.imp fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, h₂.imp fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩) h)) ?_
  refine rs_app (by simp [twos]) (by simp [gcdUV]) (twos_ct (sE _ (by decide) (by decide))) ?_
  refine rs_app (by simp [gcdUV]) (by simp) ((gcdUV_ct (sE _ (by decide) (by decide))).mono
    (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p, h₁.imp fun _ ⟨a, b, _⟩ => ⟨a, b⟩, h₂.imp fun _ ⟨a, b, _⟩ => ⟨a, b⟩⟩) h) fun _ _ h => h) ?_
  exact divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (sE [.arr aL, .arr aR, .arr aT] (by decide) (by decide)).sub (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key
