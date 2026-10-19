module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
import VerifiedGarbage.Proof.Framework.Omega

/-! # Allocate and release the nested parameter-generation stack frames -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def freeState (bytes : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s.wr.tail }

theorem alloc_frame_ok {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    {s : State} (hl : bytes ≤ (s.gpr .rsp).toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.gpr .rsp = (allocState bytes s).gpr .rsp ∧ t.wr = (allocState bytes s).wr ∧ Q (freeState bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  have hf : isa.pop (.free bytes) (allocState bytes s) t = some (freeState bytes t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hsp, hwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem freeState_rsp {bytes : Nat} {s t : State}
    (hsp : t.gpr .rsp = (allocState bytes s).gpr .rsp) :
    (freeState bytes t).gpr .rsp = s.gpr .rsp := by
  change t.gpr .rsp + BitVec.ofNat 64 bytes = _
  rw [hsp]
  change s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 bytes = _
  exact BitVec.sub_add_cancel ..

theorem freeState_wr {bytes : Nat} {s t : State}
    (hw : t.wr = (allocState bytes s).wr) : (freeState bytes t).wr = s.wr := by
  change t.wr.tail = _
  rw [hw]
  rfl

theorem outer_stack_room {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) : 296 ≤ (u.gpr .rsp).toNat := by
  rw [hg]
  change 296 ≤ (s.gpr .rsp - BitVec.ofNat 64 48).toNat
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega

end VG.Proof.Dsa.X86_64.Generation
