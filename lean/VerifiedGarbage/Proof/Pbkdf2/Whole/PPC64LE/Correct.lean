module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Iterate

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: correctness

`INT (1)` and no output written start the loop (`loopInit_ok`); after it,
`out` holds `T₁ ‖ … ‖ T_l` up to `out_len` bytes, which is PBKDF2's result
(`Whole.pbkdf2_eq`), and our caller's registers are restored (`main_ok`).
In the frame saving the link register, `pbkdf2` meets `pbkG` (`correct`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved restore_ok preserved_of)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_stwbrx)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- `INT (1)`: `Inv` before the first block. -/
theorem loopInit_ok {s : State} (h : Keyed hF s₀ s) : WP isa (.block F.loopInit) s (Inv hF s₀ 0) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  unfold Fns.loopInit
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by omega) fun s₂ u₂ => wp_stwbrx (a := sA s₀ F.intO)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r21, u₂.gpr])
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hb h.kr.wr (by omega)) fun s₃ m₃ => WP.block_nil ?_
  have fr : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have d0 : dn s₀ (F := F) 0 = 0 := by show min (0 * F.H.D) _ = 0; simp
  refine ⟨h.kr.keep (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr]) (by rw [m₃.sp, u₂.sp, u₁.sp])
      (fun r hr => by rw [m₃.gpr, u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) fr
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj hb (.inl (by omega)) (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR F s₀, by simp, part_sub (by omega)⟩),
    h.st.keep fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hb (.inl (by omega)) (by omega) (by omega)),
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r23, d0]; simp,
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r24, d0]; simp, ?_,
    by rw [Nat.zero_mul]; rfl, ?_⟩
  · rw [m₃.mem, Mem.readW_writeW_self32, u₂.other _ (by decide), u₁.gpr]; rfl
  · rw [d0]; rfl

/-- `pbkdf2` in its frame: our caller's registers are restored, and `out`
holds the derived key. -/
theorem main_ok : WP isa F.main (entry s₀) fun s' => (∀ r ∈ VG.Proof.Hmac.Stream.PPC64LE.untouched,
      s'.gpr r = s₀.gpr r) ∧ (∀ p ∈ Hash.savedAt 0, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp - 48 ∧
      bytesAt s'.mem (out s₀) (ol s₀) = (Gk hF s₀ (nbk s₀ (F := F))).take (ol s₀) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach; have hD := hz.D
  unfold Fns.main
  refine WP.seq (WP.mono (prologue_ok hF hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hi_ok hF hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loopInit_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₃) fun s₄ h₄ => ?_)
  refine restore_ok (so := 0) ⟨rfl, by decide⟩ h₄.kr.r21 (fun d _ hd => in_sc' hp hb h₄.kr.wr (by omega))
    s₀.gpr h₄.kr.saved fun s₅ hs hr hm _ _ hsp => ⟨fun r hr' => ?_, hs, by rw [hsp, h₄.kr.sp], ?_⟩
  · rw [hr r (by revert r hr'; decide), h₄.kr.un r hr']
  · rw [hm]
    have e := h₄.outB
    rwa [show dn s₀ (F := F) (nbk s₀ (F := F)) = ol s₀ from Whole.done_nb hD.1] at e

end

/-! ## The frame -/

theorem sdepth_main (hF : FnsOK F) : sdepth F.main ≤ hF.X + 96 := by
  have hu := sdepth_le_fdepth _ hF.hH.updPf
  have hud := hF.hH.updFd
  have hf := sdepth_le_fdepth F.H.finalize (by
    simp [Hash.finalize, pushFrames, Instr.isPush, VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf hF.hH])
  have hfd : F.H.finalize.fdepth ≤ 2 := by
    have := VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth hF.hH
    simp only [Hash.finalize, Code.fdepth]; omega
  have hi := sdepth_le_fdepth (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H) (by
    simp [Impl.Pbkdf2.Stream.PPC64LE.iterate, Impl.Pbkdf2.Stream.PPC64LE.iterateBody, pushFrames, Instr.isPush,
      VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.iterateMain_pf hF.hH])
  have hid : (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H).fdepth ≤ 2 := by
    have := VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.iterateMain_fdepth hF.hH
    simp only [Impl.Pbkdf2.Stream.PPC64LE.iterate, Impl.Pbkdf2.Stream.PPC64LE.iterateBody, Code.fdepth]; omega
  have hh := hF.hiSd
  simp only [Fns.main, Fns.block, Fns.callHi, Fns.callHf, Fns.callIt, Fns.outLen, Fns.outLoop, Hash.callUpd,
    sdepth, Nat.max_le] at *
  omega

variable (hF : FnsOK F)

/-- `pbkdf2`, with its frame. -/
theorem correct {s₀ : State} (h : (pbkG hF.hH.SH F.bytes (hF.X + 144)).pre s₀) :
    WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hF.hH.SH F.bytes (hF.X + 144)).post s₀ s' := by
  have hp := pre_of hF h
  have hD := (sizes hF).D
  have hsp : 48 ≤ s₀.sp.toNat := by have := hp.sp; omega
  have hsd := sdepth_main hF
  have hX := hF.hX
  unfold Fns.pbkdf2
  refine WP.seq (VG.Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameRegAny hsp (fun R hR => ?_) (WP.mono (main_ok hp) fun s' ⟨hu, hs, hsp', hb⟩ => ?_) (by omega)
  · have hsub : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ (stk hF.X s₀) := fun a ha =>
      below_sub (a := 48) (by omega) (by have := s₀.sp.isLt; omega) a
        (Proof.MdStream.PPC64LE.frame_sub s₀.sp a ha)
    rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hp.b_o.sub_left hsub
    · exact hp.b_s.sub_left hsub
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      exact preserved_of hs hu r hr
    · simp [State.write]
    · show _ = some (bytesAt s'.mem (out s₀) (ol s₀))
      rw [hb]
      refine Whole.pbkdf2_eq _ _ (by rw [hF.hH.hD]; exact hp.olD) ?_
      rw [hF.hH.hD]
      rfl

end VG.Proof.Pbkdf2.Whole.PPC64LE
