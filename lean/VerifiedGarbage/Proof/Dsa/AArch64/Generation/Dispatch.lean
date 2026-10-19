module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! Dispatch only the three reviewed parameter-generation sizes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem lengthTest_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128]) s fun t =>
      t.gpr .x3 = W 17 ∧ eval (.zero .x .x4) t = some (W 17 == 128#64) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hw : s.mem.readW (F + BitVec.ofNat 64 136) 64 = W 17 := R.fr 17 (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = W 17 ∧ eval (.zero .x .x4) t = some (W 17 == 128#64) ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (off := 136) (by decide), L.sp, L.ld (d := 136) (n := 8) (by decide), hw, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change W 17 = (128#64) ↔ W 17 = (128#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨ha, hz, hm⟩, hk⟩ => ⟨ha, hz, hm, hk⟩

theorem lengthTest256_ok {s : State} :
    WP isa (.block [.subImm .x .x4 .x3 256]) s fun t =>
      eval (.zero .x .x4) t = some (s.gpr .x3 == 256#64) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    eval (.zero .x .x4) t = some (s.gpr .x3 == 256#64) ∧ t.mem = s.mem) (by
    brun [eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change s.gpr .x3 = (256#64) ↔ s.gpr .x3 = (256#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem dispatch_ok (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (mul : Nat → Nat → Nat → Prog isa) (round : List (Prog isa))
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State} {Q : State → Prop}
    (h : GenerationMemory p W s)
    (run : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.x3, .x4] s t →
      WP isa (Impl.Dsa.AArch64.Generation.generate G1 G256 mul round p.geo.pLen p.geo.qLen) t Q) :
    WP isa (Impl.Dsa.AArch64.Generation.dispatch G1 G256 mul round) s Q := by
  obtain ⟨V, R⟩ := h.rep
  have h17 := (h.slots 17 (by simp [generationSlots])).trans p.pLenSlot
  unfold Impl.Dsa.AArch64.Generation.dispatch
  refine WP.seq (WP.mono (lengthTest_ok h.layout R) fun u ⟨ha, hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  rw [h17] at ha hz
  rcases p.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · refine WP.ite true (by apply hz.trans; rw [hp]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hp, hq] using run u mu hm ku
  · refine WP.ite false (by apply hz.trans; rw [hp]; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite true (by apply hzv.trans; rw [ha, hp]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hp, hq] using run v (mu.congr hmv kv) (hmv.trans hm) ((ku.trans kv).mono (by decide))
  · refine WP.ite false (by apply hz.trans; rw [hp]; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite false (by apply hzv.trans; rw [ha, hp]; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hp, hq] using run v (mu.congr hmv kv) (hmv.trans hm) ((ku.trans kv).mono (by decide))

end VG.Proof.Dsa.AArch64.Generation
