module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Body
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The generator stage meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

variable {pLen : Nat}

/-- No byte of `ws` but those of the stage's scratch ranges is in a region the stage changes. -/
theorem keeps_of_frame (hb : Supported pLen) {s : State} (A : StageABI pLen s) {m : Mem}
    (hf : Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (Impl.Dsa.AArch64.Generator.layout pLen).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have qn := hb.q_le
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  have part : ∀ {e k : Nat}, (e, k) ∈ (Impl.Dsa.AArch64.Generator.layout pLen).scratch →
      e + k ≤ 2 ^ 64 → ¬ (⟨off (s.gpr .x0) e, k⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
    intro e k he hek hx
    have h := hout (e, k) he
    have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := e) (k := k) (by simp only at h; omega) (by omega) hek
    exact hd _ (Region.contains_self _ _) hx
  apply hf
  intro r hr hx
  simp only [stageChanged, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact part (e := 0) (k := Impl.Dsa.Layout.activeBytes) (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, parent])
      (by decide) (by simpa [off] using hx)
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold g; omega) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold packed; omega) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact (A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega))) _ hx hc
  · exact (A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))) _ hx hc
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx

theorem correct (M : Mont) (hb : Supported pLen) (s : State) (pre : (contract pLen).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.AArch64.Generator.code M.mm pLen) s trace t ∧ abiPreserved s t ∧
      (contract pLen).post s t := by
  have A := stageABI_of pre
  obtain ⟨trace, t, he, hpre, hst, hpk, hf⟩ := alloc_frame_ok (bytes := 272) (by decide)
    (by have := A.stackLower; unfold stack at this; omega)
    (Q := fun t => abiPreserved s t ∧
      t.gpr .x0 = BitVec.ofNat 64 (if (result pLen s).isSome then 1 else 0) ∧
      (∀ a, result pLen s = some a →
        Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a) ∧
      Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem t.mem)
    (WP.mono (body_ok M hb A) fun t P => ⟨P.sp, P.wr, ⟨P.regs, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [P.sp]; exact BitVec.sub_add_cancel .., P.vectors⟩, P.status, P.packed, P.frame⟩)
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  refine ⟨?_, keeps_of_frame hb A hf, fun a ha => hpk a ha⟩
  rw [hst]
  cases (result pLen s).isSome <;> rfl

end VG.Proof.Dsa.AArch64.Generator
