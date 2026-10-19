module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Framework.Omega

/-! # Return a p-attempt result to the bounded search controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.RsaOaep.X86_64

theorem stackStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (status : Nat) (hs : status < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.rax] s t := by
  have hv : (BitVec.ofNat 32 status).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off F 152) (BitVec.ofNat 64 status)) (by
    xrun [Impl.Dsa.X86_64.Generation.stackStatus, ea_sp, L.rsp,
      L.st (d := 152) (by decide), hv]) rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) := by
    rw [hm]; exact R.wf L.geo (by decide : 19 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]; exact writeW_outside _ _ _ (by decide)

theorem controlBase_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = B) :
    WP isa (.block Impl.Dsa.X86_64.Generation.controlBase) s fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.controlBase, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.control < 2 ^ 31)]
    exact hB) rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ => ⟨hb, hm, hk⟩

theorem searchReturn_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = B)
    (hout : InRegions s.wr (off B 16) 8) :
    WP isa (.block Impl.Dsa.X86_64.Generation.searchReturn) s fun t =>
      t.gpr .rdi = B ∧ word t.mem B 16 = W 19 ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.rdi, .rax] s t := by
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem.writeW (off B 16) (W 19)) (by
    xrun [List.cons_append, List.nil_append, Impl.Dsa.X86_64.Generation.searchReturn, Impl.Dsa.X86_64.Generation.controlBase,
      ea_sp, L.rsp, State.ea, Impl.Mgf1.X86_64.sp, BitVec.ofInt_natCast, hdr, hdrOff,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      L.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.control < 2 ^ 31), hB, hout]) rfl)
    fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨hb, ?_, ?_, hk⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86_64.Generation
