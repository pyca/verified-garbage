module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Saving and restoring the caller uses only public addresses -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller

private def Loaded (L : Ws) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ s.gpr .rax = BitVec.ofNat 64 L.w

def SavePre (L : Ws) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ slot L.w 28 ≤ L.Z

private theorem save_load_ok {L : Ws} {s : State} (h : SavePre L s) :
    WP isa (.block (save.take 1)) s (Loaded L) := by
  obtain ⟨mi, hg, hz⟩ := h
  have hl := hg.scr.ld (d := 8 * sW) (by
    have := hdr_lt_slot L.w 28 (show sW < 32 by decide)
    omega_arith)
  unfold save padAddress Loaded
  simp only [List.take_succ_cons, List.take_zero, List.cons_append]
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl, hg.hdr.hw]

private theorem loaded_pins : Pins Loaded [.rdi, .rax] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.trans ht.2.symm

theorem save_ct : RelCT isa (Two SavePre) (.block save) fun _ _ => True := by
  rw [← List.take_append_drop 1 save]
  apply RelCT.block_append
  refine RelCT.seq (two_post (Ψ := Loaded) ?_ (fun _ _ h => save_load_ok h)) ?_
  · exact two_taint [.rdi] (fun L s t hs ht r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hs.choose_spec.1.rdi.trans ht.choose_spec.1.rdi.symm) (by taint_decide)
  · exact two_taint [.rdi, .rax] loaded_pins (by taint_decide)

def RestorePre (L : Ws) (s : State) : Prop :=
  Scr s L.B L.Z ∧ slot L.w 28 ≤ L.Z ∧ s.gpr .rbx = L.B ∧
    word s.mem L.B (8 * sW) = BitVec.ofNat 64 L.w

private theorem restore_head_ok {L : Ws} {s : State} (h : RestorePre L s) :
    WP isa (.block (restore.take 6)) s (Loaded L) := by
  obtain ⟨hs, hz, hb, hw⟩ := h
  have hf := hs.st (d := 8 * kFlag) (by
    have := hdr_lt_slot L.w 28 (show kFlag < 32 by decide)
    omega_arith)
  have hl := hs.ld (d := 8 * sW) (by
    have := hdr_lt_slot L.w 28 (show sW < 32 by decide)
    omega_arith)
  have hm (v : BitVec 64) :
      word (s.mem.writeW (off L.B (8 * kFlag)) v) L.B (8 * sW) = BitVec.ofNat 64 L.w :=
    ((writeW_outside s.mem L.B v (by decide : 8 * kFlag + 8 ≤ 2 ^ 64)).word
      (Or.inl (by decide : 8 * sW + 8 ≤ 8 * kFlag)) (by decide)).trans hw
  dsimp only [VG.Proof.Bignum.word] at hm
  unfold restore padAddress Loaded
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  xrun [State.ea, hdr, hdrOff, hb, hf, hl, hm]

theorem restore_ct : RelCT isa (Two RestorePre) (.block restore) fun _ _ => True := by
  rw [← List.take_append_drop 6 restore]
  apply RelCT.block_append
  refine RelCT.seq (two_post (Ψ := Loaded) ?_ (fun _ _ h => restore_head_ok h)) ?_
  · exact two_taint [.rbx] (fun L s t hs ht r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hs.2.2.1.trans ht.2.2.1.symm) (by taint_decide)
  · exact two_taint [.rdi, .rax] loaded_pins (by taint_decide)

end VG.Proof.MillerRabin.X86_64.Caller
