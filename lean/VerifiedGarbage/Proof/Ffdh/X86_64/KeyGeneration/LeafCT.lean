module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CTData
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Exits
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CTData
meta import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Exits
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # The key search's exits and rejections use only public addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.Generation (controller_zero_out)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem key_zero_x {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hdi : s.gpr .rdi = p.control) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 2) s fun t =>
      KeyLive p original used keys scalars t ∧ t.gpr .rdi = p.control := by
  have hk := h.input.len_bounds
  have scr := h.input.control_scr (t := s) h.wr
  refine WP.mono (controller_zero_out scr hdi (by decide) (sPtr := 5) (sLen := 2) (by decide)
    (by decide) (h.header (by simp [KeyPublic.headers])) (h.header (by simp [KeyPublic.headers]))
    (by omega) (by omega) (h.input.output_x h.wr)) fun _ ⟨_, hfv, kv⟩ => ?_
  exact ⟨zero_live h h.input.x_mem h.input.x_ne_ctl hfv kv, (kv.gpr (by decide)).trans hdi⟩

def KeyZeroCT (p : KeyPublic) (s : State) : Prop := KeyAny p s ∧ s.gpr .rdi = p.control

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State)
    (h : KeyZeroCT p s) :
    WP isa (.block [.mov .rsi (.mem (hdr j)), .mov .rcx (.mem (hdr 2)), .mov32 .rax (.imm 0)]) s
      fun t => t.gpr .rsi = (if j = 5 then p.xp else p.yp) ∧ t.gpr .rcx = BitVec.ofNat 64 p.len := by
  obtain ⟨⟨original, used, keys, scalars, h⟩, hd⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  have hl2 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 16) 8 := scr.ld (by decide)
  rcases hj with rfl | rfl
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
    xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl, hl2]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
    xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl, hl2]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyZeroCT) (VG.Impl.Rsa.X86_64.Keys.zeroOut j 2) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold VG.Impl.Rsa.X86_64.Keys.zeroOut <;>
  · refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.2.trans h₂.2.symm) (by taint_decide) (zero_header _ (by decide))) ?_
    exact two_taint [.rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyZeroCT p s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 2) s (KeyZeroCT p) := by
  obtain ⟨⟨original, used, keys, scalars, h⟩, hd⟩ := h
  exact WP.mono (key_zero_x h hd) fun _ ⟨ht, hdt⟩ => ⟨⟨original, used, keys, scalars, ht⟩, hdt⟩

private theorem rdi_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [.mov .rdi (.reg .r12)]) s (KeyZeroCT p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  refine WP.mono (WP.keep [.rdi] (Q := fun u => u.gpr .rdi = p.control ∧ u.mem = s.mem)
    (by xrun [h.r12]) rfl) fun _ ⟨⟨hd, hm⟩, k⟩ =>
    ⟨⟨original, used, keys, scalars, h.keep k hm (by decide)⟩, hd⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  refine RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) rdi_ready) ?_
  exact RelCT.seq (two_post (zero_ct 5 (by decide)) zero_ready) (zero_ct 6 (by decide))

private theorem terminal_ready (status : Nat) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal status)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h status) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) (terminal_ready 3))
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [.mov .rax (.mem (field 2)), .store (field 3) .rax, .mov32 .rax (.imm 0),
      .store (field 14) .rax]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.X86_64.KeyGeneration
