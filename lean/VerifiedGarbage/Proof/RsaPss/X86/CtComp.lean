module

public import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, one compression

`comp_vp`: the compression function compresses the block at `oSt + N`, right
after the hash value at `oSt`, into it, with its scratch space at `oCW` and
its frame below `esp`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Pbkdf2.Stream.X86 (After stk)
open VG.Proof.Pbkdf2.Md.X86 (CmpArgs cmp_ok cmp_rel)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The regions a compression writes. -/
abbrev compW (L : Lay) (scr : BitVec 32) : List Region := [sR scr oSt h.N, sR scr oCW h.H.so, L.LOW]

/-- One compression of the block at `oSt + N` into the hash value at `oSt`. -/
theorem comp_vp (hg : Geo L scr) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N))
      h.H.cmp
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame (compW h L scr) m₀ s.mem ∧
        h.md.stateAt s.mem (sa scr oSt) =
          h.md.compress (h.md.stateAt m₀ (sa scr oSt)) (h.md.blockAt m₀ (sa scr (oSt + h.N)))) := by
  have hN := h.N_le
  have hso := h.so_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hB0 : 0 < h.B := by omega
  have fit := hg.fit
  unfold oRsa at fit
  have a0 : sa scr oCW = scr.setWidth 64 := by simp [sa, oCW]
  have aSt : (scr + BitVec.ofNat 32 oSt).setWidth 64 = sa scr oSt := hg.scrA (by decide)
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSt →
      s.gpr .eax = scr + BitVec.ofNat 32 (oSt + h.N) →
      CmpArgs h.N h.B h.H.so s (scr + BitVec.ofNat 32 oSt) scr := fun σ s hc bx ax => by
    refine ⟨bx, by rw [ax, BitVec.add_assoc, BitVec.ofNat_add_ofNat], hc.ebp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega
    · rw [aSt]; exact Covers.one (hg.wr hc.st (by pomega))
    · rw [← a0]; exact Covers.one (hg.wr hc.st (by pomega))
    · rw [aSt, ← a0]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aSt]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [← a0]; exact (hg.low hc.st.ok (by pomega)).symm.sub_left (stk_low hg hc)
    · rw [hg.scr_lt (by decide)]; pomega
    · pomega
  refine VP.of_ct (fun _ _ => cmp_rel h.ok.comp hB0 (sp := L.B) fun a b hab =>
    ⟨args _ _ hab.1.1 hab.1.2.2.1 hab.1.2.2.2, args _ _ hab.2.1 hab.2.2.2.1 hab.2.2.2.2, hab.1.1.st.sp,
      hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hx, bx, ax⟩
  refine cmp_ok h.ok.comp hB0 (args σ s hc bx ax) fun s' af e => ?_
  have fr : Frame (compW h L scr) s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aSt]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [← a0]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), stk_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), s.mem, hx, fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hg.inW (by pomega)
    · exact hg.inW (by pomega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  rw [aSt, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa] at e
  exact e

end VG.Proof.RsaPss.X86
