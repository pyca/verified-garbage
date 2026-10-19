module
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp

import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

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
      rcases (show q.2 = 0 ∨ q.2 = 1 by omega) with h | h <;> rw [h] <;> decide
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
  have hi' : q.2 < q.1.2.length := by omega
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
    have h256 : 256 ≤ slot a.1.x.wx 8 := by unfold slot hdrBytes; omega
    have hout : ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤
        ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i) := fun i hi' => by
      have := he.out i hi'
      rcases ofs_rebase a.1.x.B (a.1.ptr + BitVec.ofNat 64 i) (o := a.1.x.o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega
      · omega
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl
      False.elim hsp hsl hep hel) fun t hI => ⟨by omega, s, minv, X, _, hI, hw2, by omega,
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega, he, hout⟩
  simp only [seqs, pubBytes]
  refine (two_loop (Φ := PBytesInv) (Ψ := fun _ _ => True) (fun a => a.1.len) (pubByte_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (pubByte_ok M hw hw' hR rfl hL' (by omega) he.rd he.val hout hI)
    fun s' ⟨hI', hz⟩ => ⟨eval_nz_count hi (by rw [← hL]; exact hz), fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR,
      hXN, hL, hL', he, hout⟩, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64.PublicPower
