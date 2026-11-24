module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Piece
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # Both buffer layouts through the whole and partial contiguous POWER seal loops -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous (cryptRest)
open VG.Proof.AesGcm.PPC64LE.DirectGather
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (Ctr)

variable {v : Reg → Addr} {sp src dst : Addr} {rounds doneBytes len : Nat} {icb : Block} {s : State}

theorem cryptRest_wp (env : Env (cursors v dst) sp s) (ptr : s.gpr .r24 = src)
    (length : s.gpr .r25 = BitVec.ofNat 64 len) (args : Range v s src dst len)
    (lay : Lay (v .r29) (v .r30) (v .r31)) (valid : rounds = 10 ∨ rounds = 12 ∨ rounds = 14)
    (key : v .r28 = BitVec.ofNat 64 rounds) (aligned : doneBytes % 16 = 0)
    (ctr : Ctr s.mem (v .r30+BitVec.ofNat 64 48) (v .r30+BitVec.ofNat 64 64)
      (ciphOf s.mem (v .r29) rounds) icb doneBytes) :
    WP isa cryptRest s (PieceOutAt v sp rounds icb doneBytes src dst len s
      (dst + BitVec.ofNat 64 (16*(len/16)))) := by
  have start : Progress v sp rounds icb doneBytes src dst len s 0 s := by
    refine ⟨Nat.zero_le _,by simpa using env,rfl,rfl,by simpa using ptr,by rwa [Nat.sub_zero],
      by rwa [Nat.add_zero],by simp [VG.Spec.Aes.bytesAt,VG.Proof.Gcm.xorKs_nil],Frame.refl _ _⟩
  refine WP.seq (WP.mono (atWhole start args lay valid key (.inr (by simpa using aligned))) fun t p => ?_)
  simp only [Nat.sub_zero,Nat.zero_add] at p
  let j := 16*(len/16)
  apply atTailWith p args lay valid key (.inr (by omega_using [aligned])) (by omega)
  let u := t.write .r26 (t.gpr .r21)
  have prep : WP isa (.block [mov .r26 .r21]) t (· = u) := by crun [mov,u,BitVec.or_self]
  obtain ⟨trace,_,run,rfl,keeps⟩ := WP.keep wholeRegs prep (by decide)
  have d : t.gpr .r21 = dst + BitVec.ofNat 64 j := p.env.fr _ (by decide)
  exact ⟨trace,u,run,d,d,rfl,rfl,rfl,keeps⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous
