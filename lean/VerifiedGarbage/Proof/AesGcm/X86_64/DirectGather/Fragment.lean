module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT

/-! Encrypt a fragment directly from its source, continuing the shared counter stream. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)

structure PieceInput (Ctx St W SP : Addr) (R : Nat) (Q D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  src : DataOk St W SP s Q n
  dst : DataW Ctx St W SP s D n
  apart : (⟨Q,n⟩ : Region).Disjoint ⟨D,n⟩
  rbx : s.gpr .rbx = Q
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n

structure PieceOutput (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat)
    (Q D : Addr) (n : Nat) (s t : State) : Prop where
  env : Env Ctx St W SP t
  rounds : RoundsAt t.mem W R
  ctr : Ctr t.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb (P+n)
  out : bytesAt t.mem D n = xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem Q n)
  frame : Frame (crFrame St W SP D n) s.mem t.mem

/-- Output of a prefix of one fragment, with both cursors ready for the remaining bytes. -/
structure SpanOutput (Ctx St W SP Q D : Addr) (R n k P : Nat) (icb : Block) (s t : State) : Prop where
  head : PieceOutput Ctx St W SP R icb P Q D k s t
  src : t.gpr .rbx = Q + BitVec.ofNat 64 k
  dst : t.gpr .r12 = D + BitVec.ofNat 64 k
  left : t.gpr .rbp = BitVec.ofNat 64 (n-k)

variable {Ctx St W SP Q D : Addr} {R n P : Nat} {s : State} {icb : Block}

private theorem PieceInput.mid (p : PieceInput Ctx St W SP R Q D n s) (align : n=0 ∨ P%16=0) :
    CrMid Ctx St W SP R icb P D n s.mem 0 s := by
  refine ⟨p.env, Nat.zero_le _, by simpa using p.r12, by simpa using p.rbp, p.dst, p.rounds,
    fun h => by simpa using h, fun _ => ?_, rfl, by simpa using align, Frame.refl _ _⟩
  simp [bytesAt, xorKs]

theorem tail_ok (v : GcmImpl) (L : Lay Ctx St W SP) (p : PieceInput Ctx St W SP R Q D n s)
    (short : n < 16) (align : n=0 ∨ P%16=0)
    (ctr : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb P) :
    WP isa (cryptTailG v.callees true) s (PieceOutput Ctx St W SP R icb P Q D n s) := by
  have src : TailSrc true St W SP s s.mem D 0 n Q := by
    simpa [TailSrc] using And.intro p.rbx (And.intro p.src p.apart)
  refine (cryptTailG_ok v L true (p.mid align) (by simpa using short) rfl src).mono fun t h =>
    ⟨h.env, h.rounds, h.ctr ctr, ?_, h.frame⟩
  simpa [bytesAt] using h.out ctr

theorem tail_rel (v : GcmImpl) (L : Lay Ctx St W SP) {t : State}
    (p : PieceInput Ctx St W SP R Q D n s) (q : PieceInput Ctx St W SP R Q D n t)
    (align : n=0 ∨ P%16=0) :
    ∀ tr u, Exec isa (cryptTailG v.callees true) s tr u →
      ∀ tr' u', Exec isa (cryptTailG v.callees true) t tr' u' → tr = tr' := by
  intro tr u a tr' u' b
  exact (cryptTailG_rel v L true (Q := Q) (icb₁ := 0) (icb₂ := 0) (P₁ := P) (P₂ := P)
    (R := R) (j := 0) (D := D) (n := n) (m₁ := s.mem) (m₂ := t.mem)
    s t tr tr' u u' ⟨⟨p.mid align, fun _ => p.rbx⟩, q.mid align, fun _ => q.rbx⟩ a b).1

end VG.Proof.AesGcm.X86_64.DirectGather
