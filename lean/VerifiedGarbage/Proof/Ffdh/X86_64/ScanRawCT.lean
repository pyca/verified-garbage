module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: timing of scans before arithmetic workspace setup -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

/-- The scan uses only the outer header and the public bound bytes. -/
def ScanRawPre (sp : Nat) (a : ScanPub) (s : State) : Prop :=
  Scr s a.B a.Z ∧ s.gpr .rdi = a.B ∧ 256 ≤ a.Z ∧
    word s.mem a.B (8 * sp) = a.p ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.bs.length ∧
    a.bs ≠ [] ∧ a.bs.length < 2 ^ 32 ∧ Src s a.B a.Z a.p a.bs ∧ sp < 32

/-- `scan sp` leaks the same in runs on the same octets. -/
theorem scan_raw_ct {sp : Nat} {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sp)), .mov .rcx (.mem (hdr sK))]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.rdi, .rsi]) (.block [.store (hdr sEp) .rsi, .store (hdr sEl) .rcx, .movzx8 .rax (at0 .rsi)]) hc₂).isSome =
      true) :
    RelCT isa (Two (ScanRawPre sp)) (seqs (scan sp)) fun _ _ => True := by
  unfold scan
  simp only [seqs]
  refine RelCT.seq (R := Two fun a t => 0 < lead a.bs + 1 ∧ ScanJ a 0 t)
    (two_piece [.rdi] (pins_of (fun a _ => a.B) fun a s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) hT₁ fun a s h => ?_)
    (RelCT.seq (R := Two fun a t => ScanJ a (lead a.bs) t)
      (two_loop (fun a => lead a.bs + 1)
        (two_taint [.rsi, .rcx] (pins_of (fun (p : ScanPub × Nat) r => if r = .rsi then off p.1.p p.2 else
            BitVec.ofNat 64 (p.1.bs.length - p.2)) fun p t h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.2.1
          · exact h.2.2.1) (by taint_decide))
        fun a j t hj h => scanJ_step a j t hj h)
      (two_taint [.rdi, .rsi] (pins_of (fun a r => if r = .rdi then a.B else off a.p (lead a.bs)) fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.2.2.2.2
        · exact h.1) hT₂))
  obtain ⟨hs, hdi, hZ, hp, hk, hne, hl, hsrc, hsp⟩ := h
  have l1 := hs.ld (d := 8 * sp) (by omega)
  have l2 := hs.ld (d := 8 * sK) (by change 152 ≤ a.Z; omega)
  exact WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = a.p ∧ t.gpr .rcx = BitVec.ofNat 64 a.bs.length ∧
      t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, l1, l2, hp, hk])
    rfl)
    fun t ⟨⟨h1, h2, hm⟩, k⟩ => ⟨by omega, by rw [h1]; simp, by rw [h2]; simp, hne, hl,
      hsrc.congr (by rw [hm]; exact InScr.refl _ _ _) k.2.1 k.2.2, (k.gpr (by decide)).trans hdi⟩

end VG.Proof.Ffdh.X86_64
