module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointHeadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.JointByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointHeadCT
meta import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant-time scanning of two equal-length exponents -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def JointBytesInv (p : JointBytesPublic) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (n xc g y : Nat) (eb fb : List Byte),
    JointByteInv t₀ (off p.x.B p.x.o) p.x.wx minv n xc g y p.ep p.fp p.len eb fb i s ∧
    2 ≤ p.x.wx ∧ p.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.x.wx)) n ∧
    eb.length = p.len ∧ fb.length = p.len ∧ p.len < 2 ^ 31 ∧
    Src t₀ p.x.B p.x.Z p.ep eb ∧ Src t₀ p.x.B p.x.Z p.fp fb ∧
    (∀ i < p.len, slot p.x.wx 8 + tabBytes p.x.wx ≤ ofs (off p.x.B p.x.o) (p.ep + BitVec.ofNat 64 i)) ∧
    (∀ i < p.len, slot p.x.wx 8 + tabBytes p.x.wx ≤ ofs (off p.x.B p.x.o) (p.fp + BitVec.ofNat 64 i))

theorem jointByte_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun (q : JointBytesPublic × Nat) s => q.2 < q.1.len ∧ JointBytesInv q.1 q.2 s)
      (seqs [.block Joint.byteHead, .loop (Joint.window Sq.mm M.mm) .ne,
        .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
          .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (q : JointBytesPublic × Nat) s => 0 < 4 ∧ JointWinI q.1.x 0 s)
    (two_map (fun q : JointBytesPublic × Nat => q)
      (fun _ _ ⟨_, _, minv, n, xc, _, _, _, _, hi, _⟩ => ⟨minv, n, xc, hi.ctx, hi.idx, hi.e, hi.f⟩)
      jointHead_ct) ?_) ?_
  · rintro q s ⟨hi, t₀, minv, n, xc, g, y, eb, fb, hI, hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩
    refine WP.mono (jointByteHeadInv_ok hL hF hi
      (by simpa only [hL] using he.rd) (by simpa only [hL] using he.val) hout
      (by simpa only [hF] using hf.rd) (by simpa only [hF] using hf.val) fout hI)
      fun t ht => ?_
    exact ⟨by decide, t, minv, n, xc, g, y, _, _, _, _, ht, hw, hw', hR,
      (eb[q.2]'(by omega)).isLt, (fb[q.2]'(by omega)).isLt⟩
  refine RelCT.seq (two_map (fun q : JointBytesPublic × Nat => q.1.x) (fun _ _ h => h)
    (jointWindows_ct M Sq)) ?_
  exact rdi_ct (fun p : XPub => off p.B p.o)
    (fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide)

theorem jointBytes_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun p s => 0 < p.len ∧ JointBytesInv p 0 s) (Joint.bytes Sq.mm M.mm)
      (Two fun p s => JointBytesInv p p.len s) := by
  apply two_loop (Φ := JointBytesInv) (fun p => p.len) (jointByte_ct M Sq)
  rintro p i s hi ⟨t₀, minv, n, xc, g, y, eb, fb, hI, hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩
  refine WP.mono (jointByte_ok M Sq hw hw' hR hL hF hL' hi
    (by simpa only [hL] using he.rd) (by simpa only [hL] using he.val) hout
    (by simpa only [hF] using hf.rd) (by simpa only [hF] using hf.val) fout hI)
    fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hi hz, ?_, ?_⟩
  · intro _
    exact ⟨t₀, minv, n, xc, g, y, eb, fb, hI', hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩
  · intro h
    exact h ▸ ⟨t₀, minv, n, xc, g, y, eb, fb, hI', hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩

end VG.Proof.Dsa.X86_64
