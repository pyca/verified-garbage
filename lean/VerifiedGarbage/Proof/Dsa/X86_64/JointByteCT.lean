module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointHeadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.JointByte
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointHeadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
