module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
meta import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCT
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Block

/-! ### `Dsa.AArch64.PublicCallCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.PublicPowerCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.PublicExponentCT`, which only this module used -/

section

/-! # Public exponentiation leaks only its public exponent and layout

As RSA's (`crtExpLoop_ct`, `Proof/Bignum/AArch64/CrtCTExp.lean`), with the
exponent's bytes in the public data: the windows' digits choose the table's
entry and whether to multiply. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

/-- A public byte through its two windows. -/
def PWinI (p : XPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc E : Nat),
    CWinInv t₀ (off p.1.B p.1.o) p.1.wx minv X Xc False 0 E p.2 j s ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) X ∧ Xc < X ∧ p.2 < 256

theorem pubWins_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 2 ∧ PWinI p 0 s) (.loop (seqs (window M.mm)) (.nonzero .x .x3))
      (Two fun p s => PWinI p 2 s) := by
  apply two_loop (Φ := PWinI) (fun _ => 2)
  · apply two_map (fun q : (XPub × Nat) × Nat => (q.1.1, q.1.2 * 16 ^ q.2)) ?_ (window_ct M)
    intro q s ⟨hj, t₀, minv, X, Xc, E, hI, hw, hw', hR, _, hv⟩
    have hp : 16 ^ q.2 ≤ 16 := by
      rcases (show q.2 = 0 ∨ q.2 = 1 by omega_using [hj]) with h | h <;> rw [h] <;> decide
    exact ⟨minv, X, Xc, hI.ctx, hI.tab, hI.ylt, hI.v,
      by have := Nat.mul_le_mul_left q.1.2 hp; omega, hw, hw', hR⟩
  · intro p j s hj ⟨t₀, minv, X, Xc, E, hI, hw, hw', hR, hXN, hv⟩
    exact WP.mono (pubWinStep_ok M hw hw' hR hv hj hI) fun _ ⟨hI', hz⟩ =>
      ⟨eval_nz_count hj hz, fun _ => ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩,
        fun h => h ▸ ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩⟩

/-- After `i` bytes of the public exponent `a.2`. -/
def PBytesInv (a : BPub × List Byte) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat),
    CByteInv t₀ (off a.1.x.B a.1.x.o) a.1.x.wx minv X Xc False 0 a.1.ptr a.2.length a.2 i s ∧ 2 ≤ a.1.x.wx ∧
    a.1.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.1.x.wx)) X ∧ Xc < X ∧
    a.2.length = a.1.len ∧ a.2.length < 2 ^ 31 ∧ Src t₀ a.1.x.B a.1.x.Z a.1.ptr a.2 ∧
    ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤ ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i)

/-- After the byte's address: it, and the rest of the head. -/
def PHeadMid (q : (BPub × List Byte) × Nat) (s : State) : Prop :=
  s.gpr .x0 = off q.1.1.x.B q.1.1.x.o ∧ s.gpr .x3 = q.1.1.ptr + BitVec.ofNat 64 q.2 ∧
    WP isa (.block byteLoad) s fun t => 0 < 2 ∧ PWinI (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat) 0 t

theorem pins_pBytes :
    Pins (fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ PBytesInv q.1 q.2 s) [.x0] :=
  pins_x0B (fun q : (BPub × List Byte) × Nat => off q.1.1.x.B q.1.1.x.o)
    fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.x0

theorem pins_pHeadMid : Pins PHeadMid [.x0, .x3] := by
  rintro q s₁ s₂ ⟨a₁, b₁, -⟩ ⟨a₂, b₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]

/-- The byte's address, and the rest of the head by `crtByteHead_ok`. -/
theorem pubByteAddr_ok {q : (BPub × List Byte) × Nat} {s : State}
    (h : q.2 < q.1.1.len ∧ PBytesInv q.1 q.2 s) :
    WP isa (.block byteAddr) s (PHeadMid q) := by
  obtain ⟨hi, t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, -, he, hout⟩ := h
  have hc := hI.ctx
  have hi' : q.2 < q.1.2.length := by omega_using [hi, hL]
  have hw₁ := WP.block_append_iff.mp (crtByteHead_eq ▸ crtByteHead_ok rfl hi' he.rd he.val hout hI)
  refine WP.mono (wp_and hw₁ (byteAddr_run hc hI.e hI.idx)) fun t ⟨h₂, h3, k⟩ =>
      ⟨(k.gpr .x0 (by decide)).trans hc.good.x0, h3, WP.mono h₂ fun t' ⟨_, _, hB⟩ =>
        ⟨by decide, t', minv, X, Xc, _, by simpa only [List.getElem?_eq_getElem hi', Option.getD_some] using hB,
          hw, hw', hR, hXN, (q.1.2[q.2]?.getD 0).isLt⟩⟩

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same public exponent bytes, pointer and length. -/
theorem pubByte_ct (M : Mont) :
    RelCT isa (Two fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ PBytesInv q.1 q.2 s)
      (seqs [.block byteHead, .loop (seqs (window M.mm)) (.nonzero .x .x3), .block byteNext])
      fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have h₃ : RelCT isa (Two fun (p : XPub × Nat) s => PWinI p 2 s) (.block byteNext) fun _ _ => True :=
    x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.x0)
      (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece _ pins_pBytes (by taint_decide) fun _ _ h => pubByteAddr_ok h)
      (two_piece _ pins_pHeadMid (by taint_decide) fun _ _ h => h.2.2)))
    (RelCT.seq (two_map (fun q : (BPub × List Byte) × Nat => (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat))
      (fun _ _ h => h) (pubWins_ct M)) h₃)

/-- `crtExpLoop_ok`'s hypotheses, the exponent's bytes public. -/
def PEPre (sp sl : Nat) (p : BPub × List Byte) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat),
    SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx minv ∧ 2 ≤ p.1.x.wx ∧ p.1.x.wx ≤ p.1.x.w ∧
    p.1.x.w < 2 ^ 30 ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN) p.1.x.wx = X ∧
    ((word s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx % X = x * 2 ^ (64 * p.1.x.wx) % X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx % X = y * 2 ^ (64 * p.1.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ word s.mem p.1.x.B (8 * sp) = p.1.ptr ∧
    word s.mem p.1.x.B (8 * sl) = BitVec.ofNat 64 p.2.length ∧ p.2.length = p.1.len ∧ 1 ≤ p.2.length ∧
    p.2.length ≤ 1024 ∧ Src s p.1.x.B p.1.x.Z p.1.ptr p.2

theorem PEPre.secret {sp sl : Nat} {p : BPub × List Byte} {s : State} (h : PEPre sp sl p s) :
    EPre sp sl p.1 s := by
  obtain ⟨minv, X, x, y, hrest⟩ := h
  exact ⟨minv, X, x, y, p.2, hrest⟩

/-- The public exponentiation is constant time for public exponents, given
that the taint analysis checks its start after the link's load. -/
theorem pubExpLoop_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [Crt.ldw .x3 .x5 sp, sth .x3 Crt.sExp, Crt.ldw .x3 .x5 sl,
      sth .x3 Crt.sExpLen, movi .x3 0, sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (PEPre sp sl)) (seqs (VG.Impl.Dsa.AArch64.PublicPower.expLoop M.mm sp sl))
      fun _ _ => True := by
  rw [pubExpLoop_eq, ← List.cons_append]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun a s => 0 < a.1.len ∧ PBytesInv a 0 s) ?_ fun a s h => ?_) ?_)
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [tabBuild_eq, tabPre])
      (RelCT.seq (two_post (Ψ := fun a s => TPre a.1.x s)
      ?_ fun _ _ h => by simp only [seqs]; exact crtExpInit_tpre h.secret)
      (two_map (fun a : BPub × List Byte => a.1.x) (fun _ _ h => h) (tabBuild_ct M)))
    simp only [seqs, expInit]
    exact RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
      (RelCT.seq (two_piece (Ψ := fun (a : BPub × List Byte) t => t.gpr .x0 = off a.1.x.B a.1.x.o ∧
          t.gpr .x5 = a.1.x.B) [.x0]
        (pins_x0B (fun a : BPub × List Byte => off a.1.x.B a.1.x.o) fun a s (h : PEPre sp sl a s) =>
          let ⟨_, _, _, _, hc, _⟩ := h; hc.x0) (by taint_decide)
        fun a s (h : PEPre sp sl a s) => crtLink_ok h.secret)
      (two_taint [.x0, .x5] (pins_of (fun a r => if r = .x0 then off a.1.x.B a.1.x.o else a.1.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · obtain ⟨minv, X, x, y, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1, hL2,
      he⟩ := h
    have hPn := hc.scrT.nowrap
    have hBn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h256 : 256 ≤ slot a.1.x.wx 8 := by unfold slot hdrBytes; omega_using []
    have hout : ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤
        ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i) := fun i hi' => by
      have := he.out i hi'
      rcases ofs_rebase a.1.x.B (a.1.ptr + BitVec.ofNat 64 i) (o := a.1.x.o) (by omega_using [hBn, hi, h256]) with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega_using [hi, this, h2]
      · omega_using [hi, this, h1]
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl
      False.elim hsp hsl hep hel) fun t hI => ⟨by omega, s, minv, X, _, hI, hw2, by omega_using [hwx, hw30],
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega_using [hL2], he, hout⟩
  simp only [seqs, pubBytes]
  refine (two_loop (Φ := PBytesInv) (Ψ := fun _ _ => True) (fun a => a.1.len) (pubByte_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (pubByte_ok M hw hw' hR rfl hL' (by omega_using [hi, hL]) he.rd he.val hout hI)
    fun s' ⟨hI', hz⟩ => ⟨eval_nz_count hi (by rw [← hL]; exact hz), fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR,
      hXN, hL, hL', he, hout⟩, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64.PublicPower

end

end

/-! # Timing of public exponentiation with secret bases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

def EncodedPre (p : PowerPublic × List Byte) (s : State) : Prop :=
  ∃ x : Nat, PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx Crt.aXc) p.1.bytes.x.wx =
      x * 2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aY) p.1.bytes.x.wx =
      2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus

/-- Exponentiation and decoding together have a secret-independent trace. -/
theorem encodedPower_ct (M : Mont) : RelCT isa (Two EncodedPre)
    (VG.Impl.Dsa.AArch64.PublicPower.encodedPower M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.encodedPower
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.bytes.x.ws s)
    (two_map (fun p : PowerPublic × List Byte => (p.1.bytes, p.2)) ?_ (pubExpLoop_ct M (by taint_decide))) ?_)
    (two_map (fun p : PowerPublic × List Byte => p.1.bytes.x.ws) (fun _ _ h => h)
      (M.ct (by unfold MmUse; decide)))
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, hlen, h1, h2, hs⟩, hx, hy⟩
    refine ⟨p.1.minv, p.1.modulus, x, 1, hc, p.1.lower, p.1.fits, p.1.upper,
      hm.modulus, hm.inverse, p.1.odd, ?_, ?_, ?_, ?_, by decide, by decide,
      hp, hl, hlen, h1, h2, hs⟩
    · rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · rw [hx, Nat.mod_mod]
    · rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · rw [hy, Nat.mod_mod, Nat.one_mul]
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, _, h1, h2, hs⟩, hx, hy⟩
    refine WP.mono (expLoop_ok M (x := x) hc p.1.lower p.1.fits p.1.upper hm.modulus hm.inverse p.1.odd
      (by rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this]))
      (by rw [hx, Nat.mod_mod])
      (by rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this]))
      (by rw [hy, Nat.mod_mod]) (by decide) (by decide) hp hl h1 h2 hs)
      fun t ⟨ht, _⟩ => ⟨p.1.minv, ht.good, Nat.le_refl _⟩

/-- Prepared ordinary bases for the complete encode/exponentiate/decode core. -/
def PowerCorePre (p : PowerPublic × List Byte) (s : State) : Prop :=
  PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aR2) p.1.bytes.x.wx =
      2 ^ (128 * p.1.bytes.x.wx) % p.1.modulus

/-- The whole power core is constant time for secret bases and fixed public exponents. -/
theorem powerCore_ct (M : Mont) : RelCT isa (Two PowerCorePre)
    (VG.Impl.Dsa.AArch64.PublicPower.powerCore M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.powerCore
  refine RelCT.seq (two_post (Ψ := EncodedPre)
    (two_map (fun p : PowerPublic × List Byte => p.1.product) ?_ (encodePower_ct M)) ?_)
    (encodedPower_ct M)
  · intro p s ⟨⟨_, hm, hone, _⟩, hr2⟩
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · dsimp only [PowerPublic.product]
      rw [hone]; exact p.1.greater
  · intro p s ⟨⟨hc, hm, hone, hp, hl, hlen, h1, h2, hs⟩, hr2⟩
    rw [show 128 * p.1.bytes.x.wx = 64 * p.1.bytes.x.wx + 64 * p.1.bytes.x.wx by omega_using [], Nat.pow_add] at hr2
    refine WP.mono (encodePower_ok M hm (Nat.le_refl _) p.1.lower
      (by have := p.1.fits; have := p.1.upper; omega_arith) p.1.greater p.1.odd rfl hr2 hone)
      fun t ⟨hmt, hx, hy, htone, hf, hk⟩ => ?_
    have hct := arrays_context hc hf (by decide) hk
    have hfw := arrays_work hf (by decide)
    exact ⟨_, ⟨hct, hmt, htone, (work_parent hc hfw (by decide)).trans hp,
      (work_parent hc hfw (by decide)).trans hl, hlen, h1, h2, work_source hc hfw hk hs⟩, hx, hy⟩


end VG.Proof.Dsa.AArch64.PublicPower

end

end

/-! # Public exponent bytes across Montgomery setup and input loading -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

def PowerCallBytes (p : PowerCallPublic × List Byte) (s : State) : Prop := ∃ bb : List Byte,
  word s.mem p.1.x.B (8 * arg) = p.1.base ∧ word s.mem p.1.x.B (8 * argLen) = BitVec.ofNat 64 bb.length ∧
  word s.mem p.1.x.B (8 * arg2) = p.1.bytes.ptr ∧ word s.mem p.1.x.B (8 * arg2Len) = BitVec.ofNat 64 p.2.length ∧
  bb.length = p.1.baseLen ∧ p.2.length = p.1.bytes.len ∧
  Src s p.1.x.B p.1.x.Z p.1.base bb ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2

def PowerCallPre (p : PowerCallPublic × List Byte) (s : State) : Prop :=
  SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv ∧
  ModCtx s (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus ∧ PowerCallBytes p s

def PowerCallPrepared (p : PowerCallPublic × List Byte) (s : State) : Prop := PowerCallPre p s ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aOne) p.1.x.wx = 1 ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aR2) p.1.x.wx = 2 ^ (128 * p.1.x.wx) % p.1.modulus

theorem PowerCallBytes.frame {p : PowerCallPublic × List Byte} {s t : State} (h : PowerCallBytes p s)
    (hc : SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv)
    (hf : Frm (off p.1.x.B p.1.x.o) (workRanges p.1.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    PowerCallBytes p t := by
  obtain ⟨bb, hp, hl, hep, hel, hbl, helen, hb, he⟩ := h
  exact ⟨bb, (work_parent hc hf (by decide)).trans hp, (work_parent hc hf (by decide)).trans hl,
    (work_parent hc hf (by decide)).trans hep, (work_parent hc hf (by decide)).trans hel,
    hbl, helen, work_source hc hf hk hb, work_source hc hf hk he⟩

theorem powerCall_prepare (M : Mont) {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPre p s) :
    WP isa (Arithmetic.constants M.mm) s (PowerCallPrepared p) := by
  refine WP.mono (prepare_ok M h.1 p.1.lower p.1.width48 p.1.greater p.1.odd h.2.1.modulus h.2.1.inverse)
    fun t ⟨hc, hm, hone, hr2, hf, hk⟩ => ?_
  exact ⟨⟨hc, hm, h.2.2.frame h.1 hf hk⟩, hone, hr2⟩

theorem powerCall_load {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPrepared p s) :
    WP isa (Arithmetic.load aX arg argLen) s (PowerCorePre (p.1.toPowerPublic, p.2)) := by
  obtain ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hone, hr2⟩ := h
  have hb1 : 1 ≤ bb.length := hbl ▸ p.1.basePositive
  have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
  have hb31 : bb.length < 2 ^ 31 := by
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega_using [hbw, hw48]
  refine WP.mono (load_ok hc p.1.lower p.1.fits p.1.upper (by decide) (by decide) (by decide) hp hl hb hb1 hb31 hbw)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.1.x.B p.1.x.o) p.1.x.wx [aX] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hf (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hc.good.scr.nowrap
  have hmt : ModCtx t (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by have := p.1.lower; omega_using [hb1, hbw])]
    exact hm.inverse
  refine ⟨⟨hct, hmt, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hone,
    (work_parent hc hfw (by decide)).trans hep, (work_parent hc hfw (by decide)).trans hel,
    helen, helen ▸ p.1.expPositive, helen ▸ p.1.expLimit, work_source hc hfw hk he⟩,
    (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hr2⟩

theorem powerCall_ct (M : Mont) : RelCT isa (Two PowerCallPre)
    (VG.Impl.Dsa.AArch64.PublicPower.power M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.power
  refine RelCT.seq (two_post (Ψ := PowerCallPrepared)
    (two_map (fun p : PowerCallPublic × List Byte => p.1.toPowerPublic.product) (fun p s h =>
      ⟨h.2.1, p.1.width48, p.1.greater, p.1.odd⟩) (constants_ct M)) (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => PowerCorePre (p.1.toPowerPublic, p.2) s)
    (two_map (fun p : PowerCallPublic × List Byte => (⟨p.1.x, p.1.base, p.1.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => powerCall_load h)) ?_
  · intro p s ⟨⟨hc, _, bb, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.1.minv, bb, hc, p.1.lower, p.1.fits, p.1.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.1.basePositive, ?_, hbl ▸ p.1.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega_using [hbw, hw48]
  · exact two_map (fun p : PowerCallPublic × List Byte => (p.1.toPowerPublic, p.2)) (fun _ _ h => h) (powerCore_ct M)

end VG.Proof.Dsa.AArch64.PublicPower

end

end

/-! # Public exponent bytes across the DSA calling convention -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

/-- Two readable byte strings at the same address and width agree. -/
theorem source_unique {s : State} {B p : Addr} {Z : Nat} {a b : List Byte}
    (ha : Src s B Z p a) (hb : Src s B Z p b) (hlen : a.length = b.length) : a = b := by
  apply List.ext_getElem hlen
  intro i hi hj
  exact (ha.val i hi).symm.trans (hb.val i hj)

def PowerFinishPre (p : PowerFinishPublic × List Byte) (s : State) : Prop :=
  PowerCallPre (p.1.toPowerCallPublic, p.2) s ∧ FinishPre p.1.result s

theorem powerFinish_ct (M : Mont) : RelCT isa (Two PowerFinishPre)
    (.seq (VG.Impl.Dsa.AArch64.PublicPower.power M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.1.result s)
    (two_map (fun p : PowerFinishPublic × List Byte => (p.1.toPowerCallPublic, p.2)) (fun _ _ h => h.1) (powerCall_ct M)) ?_)
    (two_map (fun p : PowerFinishPublic × List Byte => p.1.result) (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M hc p.1.lower p.1.width48 p.1.fits p.1.upper p.1.greater p.1.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.1.basePositive) (hbl ▸ p.1.baseFits)
    hep hel he (helen ▸ p.1.expPositive) (helen ▸ p.1.expLimit))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

def CallPre (a b output : Operand) (p : Call3Public × List Byte) (s : State) : Prop :=
  Call3Pre a b output p.1 s ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2 ∧ p.2.length = p.1.bytes.len

theorem callHead_public {p : Call3Public × List Byte} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallPre a b output p s) :
    WP isa (.block (callHead a b output p.1.x.o)) s (PowerFinishPre (p.1.toPowerFinishPublic, p.2)) := by
  obtain ⟨h, he, hlen⟩ := h
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩, hfr, hk⟩ => ?_
  have het := arguments_source hfr hk (Nat.le_trans (by decide) p.1.extent) he
  have eqb := source_unique hes het (helen.trans hlen.symm)
  subst eb
  exact ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩

theorem corePublicPow_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => CallPre a b output p s ∧ p.1.x.o = o)
      (Core.publicPow M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (VG.Impl.Dsa.AArch64.PublicPower.power M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre (p.1.toPowerFinishPublic, p.2) s)
    (two_map (fun p : Call3Public × List Byte => p.1) (fun _ _ h => h.1.1) (callHead_ct hT)) ?_)
    (two_map (fun p : Call3Public × List Byte => (p.1.toPowerFinishPublic, p.2)) (fun _ _ h => h) (powerFinish_ct M))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_public ha hb ho h

def ReadyPublicPre (side : ModulusSide) (d : Nat) (a b : Operand)
    (p : ReadyCallPublic side d × List Byte) (s : State) : Prop :=
  ReadyCallPre side d a b p.1 s ∧ OperandBytes s p.1.layout.base activeBytes b p.2 ∧ p.2.length = p.1.exponentLen

theorem readyPublicPow_ct (M : Mont) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyPublicPre side d a b))
      (Core.publicPow M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  apply two_map (fun p : ReadyCallPublic side d × List Byte => (p.1.call a b, p.2)) ?_
    (corePublicPow_ct M (output := ⟨.local d, side.lengthField⟩) ha hb hd hT)
  intro p s ⟨h, he, hlen⟩
  refine ⟨⟨readyCall_pre hpa hpb h, ?_, hlen⟩, rfl⟩
  have hp := h.1.publicPointer b.pointer hpb
  simpa only [hp, ReadyCallPublic.call, PowerCallPublic.x] using he.source

end VG.Proof.Dsa.AArch64.PublicPower
