module

import VerifiedGarbage.Proof.Dsa.AArch64.JointByteHead
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindowCT
public import VerifiedGarbage.Proof.Dsa.AArch64.JointByte
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointWindowCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointByte
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time scanning of two equal-length exponents

As RSA's bytes (`crtByte_ct`): the bytes are read at public addresses (the
exponents' pointers plus the byte index), which the head computes before
it loads them. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The public part of both exponents: the workspace, the pointers and the
length. -/
structure JointBytesPublic where
  x : XPub
  ep : Addr
  fp : Addr
  len : Nat

/-- After `i` bytes of both exponents. -/
def JointBytesInv (p : JointBytesPublic) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (n xc g y : Nat) (eb fb : List Byte),
    JointByteInv t₀ (off p.x.B p.x.o) p.x.wx minv n xc g y p.ep p.fp p.len eb fb i s ∧
    2 ≤ p.x.wx ∧ p.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.x.wx)) n ∧
    eb.length = p.len ∧ fb.length = p.len ∧ p.len < 2 ^ 31 ∧
    Src t₀ p.x.B p.x.Z p.ep eb ∧ Src t₀ p.x.B p.x.Z p.fp fb ∧
    (∀ i < p.len, slot p.x.wx 8 + tabBytes p.x.wx ≤ ofs (off p.x.B p.x.o) (p.ep + BitVec.ofNat 64 i)) ∧
    (∀ i < p.len, slot p.x.wx 8 + tabBytes p.x.wx ≤ ofs (off p.x.B p.x.o) (p.fp + BitVec.ofNat 64 i))

/-- Both bytes' addresses. -/
def jointByteAddr : List Instr :=
  [ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4, ldh .x5 Joint.sExp2, .add .x .x5 .x5 .x4]

/-- Both bytes into `sV`, and the window count. -/
def jointByteLoad : List Instr :=
  [.ldrb .x3 .x3 0, .ldrb .x5 .x5 0, .lsl .x .x3 .x3 8, .add .x .x3 .x3 .x5, sth .x3 Crt.sV, movi .x3 4,
    sth .x3 Crt.sBit]

theorem jointByteHead_eq : Joint.byteHead = jointByteAddr ++ jointByteLoad := rfl

/-- After both addresses: them, and the rest of the head. -/
def JHeadMid (q : JointBytesPublic × Nat) (s : State) : Prop :=
  s.gpr .x0 = off q.1.x.B q.1.x.o ∧ s.gpr .x3 = q.1.ep + BitVec.ofNat 64 q.2 ∧
    s.gpr .x5 = q.1.fp + BitVec.ofNat 64 q.2 ∧
    WP isa (.block jointByteLoad) s fun t => 0 < 4 ∧ JointWinI q.1.x 0 t

theorem pins_jBytes :
    Pins (fun (q : JointBytesPublic × Nat) s => q.2 < q.1.len ∧ JointBytesInv q.1 q.2 s) [.x0] :=
  pins_x0B (fun q : JointBytesPublic × Nat => off q.1.x.B q.1.x.o)
    fun _ _ ⟨_, _, _, _, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0

theorem pins_jHeadMid : Pins JHeadMid [.x0, .x3, .x5] := by
  rintro q s₁ s₂ ⟨a₁, b₁, c₁, -⟩ ⟨a₂, b₂, c₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]

/-- Both addresses, in the workspace at `P`. -/
theorem jointByteAddr_run {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {ep fp : Addr} {i : Nat} (he : word t.mem P (8 * Crt.sExp) = ep)
    (hf : word t.mem P (8 * Joint.sExp2) = fp) (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block jointByteAddr) t fun t' => (t'.gpr .x3 = ep + BitVec.ofNat 64 i ∧
      t'.gpr .x5 = fp + BitVec.ofNat 64 i) ∧ Keep [.x3, .x4, .x5] t t' := by
  refine WP.keep [.x3, .x4, .x5] ?_ (by decide) (by decide) (by decide +kernel)
  brun [jointByteAddr, hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Joint.sExp2 < 32 by decide), hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Joint.sExp2) (by decide), he, hf, hi]

/-- Both addresses, and the rest of the head by `jointByteHeadInv_ok`. -/
theorem jointByteAddr_ok {q : JointBytesPublic × Nat} {s : State}
    (h : q.2 < q.1.len ∧ JointBytesInv q.1 q.2 s) :
    WP isa (.block jointByteAddr) s (JHeadMid q) := by
  obtain ⟨hi, t₀, minv, n, xc, g, y, eb, fb, hI, hw, hw', hR, hL, hF, -, he, hf, hout, fout⟩ := h
  have hc := hI.ctx
  have hw₁ := WP.block_append_iff.mp (jointByteHead_eq ▸ jointByteHeadInv_ok hL hF hi
    (by simpa only [hL] using he.rd) (by simpa only [hL] using he.val) hout
    (by simpa only [hF] using hf.rd) (by simpa only [hF] using hf.val) fout hI)
  refine WP.mono (wp_and hw₁ (jointByteAddr_run hc hI.e hI.f hI.idx)) fun t ⟨h₂, ⟨h3, h5⟩, k⟩ =>
    ⟨(k.gpr .x0 (by decide)).trans hc.good.x0, h3, h5, WP.mono h₂ fun t' hB =>
      ⟨by decide, t', minv, n, xc, g, y, _, _, _, _, hB, hw, hw', hR,
        (eb[q.2]'(by omega_arith)).isLt, (fb[q.2]'(by omega_arith)).isLt⟩⟩

/-- One pair of bytes leaks the same in runs with the same workspace and the
same exponents' pointers and length. -/
theorem jointByte_ct (M : Mont) :
    RelCT isa (Two fun (q : JointBytesPublic × Nat) s => q.2 < q.1.len ∧ JointBytesInv q.1 q.2 s)
      (seqs [.block Joint.byteHead, .loop (seqs (Joint.window M.mm)) (.nonzero .x .x3),
        .block Joint.byteNext]) (fun _ _ => True) := by
  simp only [seqs]
  rw [jointByteHead_eq]
  have h₃ : RelCT isa (Two fun (p : XPub) s => JointWinI p 4 s) (.block Joint.byteNext) fun _ _ => True :=
    x0_ct (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0)
      (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece _ pins_jBytes (by taint_decide) fun _ _ h => jointByteAddr_ok h)
      (two_piece _ pins_jHeadMid (by taint_decide) fun _ _ h => h.2.2.2)))
    (RelCT.seq (two_map (fun q : JointBytesPublic × Nat => q.1.x) (fun _ _ h => h) (jointWindows_ct M)) h₃)

theorem jointBytes_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.len ∧ JointBytesInv p 0 s) (Joint.bytes M.mm)
      (Two fun p s => JointBytesInv p p.len s) := by
  apply two_loop (Φ := JointBytesInv) (fun p => p.len) (jointByte_ct M)
  rintro p i s hi ⟨t₀, minv, n, xc, g, y, eb, fb, hI, hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩
  refine WP.mono (jointByte_ok M hw hw' hR hL hF hL' hi
    (by simpa only [hL] using he.rd) (by simpa only [hL] using he.val) hout
    (by simpa only [hF] using hf.rd) (by simpa only [hF] using hf.val) fout hI)
    fun t ⟨hI', hz⟩ => ⟨eval_nz_count hi hz, ?_, ?_⟩
  · intro _
    exact ⟨t₀, minv, n, xc, g, y, eb, fb, hI', hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩
  · intro h
    exact h ▸ ⟨t₀, minv, n, xc, g, y, eb, fb, hI', hw, hw', hR, hL, hF, hL', he, hf, hout, fout⟩

end VG.Proof.Dsa.AArch64
