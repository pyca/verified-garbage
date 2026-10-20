module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Dispatch only the three reviewed parameter-generation sizes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem lengthTest_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block [.mov .rax (.mem (sp 136)), .alu .cmp .rax (.imm 128)]) s fun t =>
      t.gpr .rax = W 17 ∧ t.zf = some (W 17 == 128) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = W 17 ∧ t.zf = some (W 17 == 128) ∧ t.mem = s.mem) (by
      xrun [ea_sp, L.rsp, L.ld (d := 136) (by decide), R.slot (d := 136) (k := 17) rfl (by decide) rfl]
      rw [sub_beq_zero]; rfl) rfl) fun _ ⟨⟨ha, hz, hm⟩, hk⟩ => ⟨ha, hz, hm, hk⟩

theorem lengthTest256_ok {s : State} :
    WP isa (.block [.alu .cmp .rax (.imm 256)]) s fun t =>
      t.zf = some (s.gpr .rax == 256) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (s.gpr .rax == 256) ∧ t.mem = s.mem) (by xrun; rw [sub_beq_zero]; rfl) rfl)
    fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem dispatch_ok (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State} {Q : State → Prop}
    (h : GenerationMemory p W s)
    (run : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.rax] s t →
      WP isa (Impl.Dsa.X86_64.Generation.generate G1 G256 sq mul round p.geo.pLen p.geo.qLen) t Q) :
    WP isa (Impl.Dsa.X86_64.Generation.dispatch G1 G256 sq mul round) s Q := by
  obtain ⟨V, R⟩ := h.rep
  have h17 := (h.slots 17 (by simp [generationSlots])).trans p.pLenSlot
  unfold Impl.Dsa.X86_64.Generation.dispatch
  refine WP.seq (WP.mono (lengthTest_ok h.layout R) fun u ⟨ha, hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  rw [h17] at ha hz
  rcases p.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · refine WP.ite true (by simp [eval, hz, hp]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hp, hq] using run u mu hm ku
  · refine WP.ite false (by simp [eval, hz, hp]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite true (by simp [eval, hzv, ha, hp]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hp, hq] using run v (mu.congr hmv kv) (hmv.trans hm) ((ku.trans kv).mono (by decide))
  · refine WP.ite false (by simp [eval, hz, hp]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite false (by simp [eval, hzv, ha, hp]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hp, hq] using run v (mu.congr hmv kv) (hmv.trans hm) ((ku.trans kv).mono (by decide))

end VG.Proof.Dsa.X86_64.Generation
