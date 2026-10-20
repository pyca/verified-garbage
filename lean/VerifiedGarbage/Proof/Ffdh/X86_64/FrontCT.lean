module

import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: the domain front in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A public workspace pointer. -/
theorem pins_rdiB {α : Type} {Φ : α → State → Prop} (f : α → Addr)
    (h : ∀ a s, Φ a s → s.gpr .rdi = f a) : Pins Φ [.rdi] :=
  pins_of (fun a _ => f a) fun a s ha r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h a s ha

private abbrev domPtrs : List Instr :=
  [.mov .rdx (.mem (hdr sDom)), .mov .rcx (.mem (hdr sK)), .mov .rax (.reg .rdx),
    .alu .add .rax (.reg .rcx), .store (hdr sG) .rax, .alu .add .rax (.reg .rcx), .store (hdr sQ) .rax]

private theorem domPtrs_ok (a : DPub) (s : State) (h : DHP a s) :
    WP isa (.block domPtrs) s fun t => t.gpr .rdx = a.dp ∧ t.gpr .rcx = BitVec.ofNat 64 a.k := by
  obtain ⟨hs, hdi, hZ, hD, hK⟩ := h
  exact WP.mono (WP.keep [.rax, .rdx, .rcx]
    (Q := fun t => t.gpr .rdx = a.dp ∧ t.gpr .rcx = BitVec.ofNat 64 a.k)
    (by unfold domPtrs; xrun [State.ea, hdr, hdi, hdrOff,
      hs.ld (d := 8 * sDom) (by change 136 ≤ a.Z; omega), hs.ld (d := 8 * sK) (by change 152 ≤ a.Z; omega),
      hs.st (d := 8 * sG) (by change 224 ≤ a.Z; omega), hs.st (d := 8 * sQ) (by change 232 ≤ a.Z; omega), hD, hK]) rfl)
    fun _ h => h.1

theorem domHead_ct : RelCT isa (Two DHP) (.block domHead) fun _ _ => True := by
  change RelCT isa (Two DHP) (.block (domPtrs ++ invalid)) _
  refine RelCT.block_append (RelCT.seq
    (two_piece [.rdi] (pins_rdiB DPub.B fun _ _ h => h.2.1) (by taint_decide) domPtrs_ok)
    (two_taint [.rdx, .rcx] (pins_of (fun (a : DPub) r => if r = .rdx then a.dp else BitVec.ofNat 64 a.k)
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))

theorem setup_ct :
    RelCT isa (Two SetupP) (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup))
      fun _ _ => True := by
  refine RelCT.seq (R := Two SP1)
    (two_piece [.rdi] (pins_rdiB DPub.B fun _ _ ⟨_, _, hdi, _⟩ => hdi) (by taint_decide) sp0_sp1) ?_
  exact two_map DPub.m sp1_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.X86_64
