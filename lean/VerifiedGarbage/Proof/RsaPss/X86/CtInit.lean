module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, the hash value

`init_vp`: the streaming `init` sets the hash value at `oSt` to the initial
one. The 48 bytes below the stack pointer, where the calls of the hash
function's code put their frames, are in our callees' stack (`stk_low`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs After init_frame init_rel stk)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The 48 bytes below the stack pointer, where a call's frame goes, are in
our callees' stack. -/
theorem stk_low (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) : Region.Sub (stk s) L.LOW := by
  have hC := hg.C48
  have ok := hc.st.ok
  rw [stk, hc.st.sp, ← ok.low_eq]
  exact below_sub hC ok.BC

/-- `esp` and `ebp` agree in two states of the body. -/
theorem sp_bp {F : State → State → Prop} (hF : ∀ σ s, F σ s → Ctx L scr σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp, .ebp], s₁.gpr r = s₂.gpr r :=
  fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hF _ _ h₁).st.sp, (hF _ _ h₂).st.sp]
    · rw [(hF _ _ h₁).ebp, (hF _ _ h₂).ebp]

/-- The streaming `init` on the hash value at `oSt`. -/
theorem init_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt (h.N + h.B), L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem) (initPart h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) := by
  have hN := h.N_le
  have hBl := h.B_le
  have fit := hg.fit
  have hS := h.S_eq
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .ebx = scr + BitVec.ofNat 32 oSt)
    (VP.taint [.esp, .ebp] initArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi⟩ => ?_) ?_
  · refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => WP.block_nil ⟨(hc.upd u1 (by decide) (by decide)).upd u2
      (by decide) (by decide), by rw [u2.mem, u1.mem]; exact hi, by rw [u2.gpr, u1.gpr, hc.ebp]⟩
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + h.H.S ≤ 2 ^ 32 := by
    rw [hg.scr_lt (by decide), hS]; unfold oSt oRsa at *; omega
  have hsub : Region.Sub ⟨(scr + BitVec.ofNat 32 oSt).setWidth 64, h.H.S⟩ (sR scr oSt (h.N + h.B)) := by
    rw [hg.scrA (by decide), hS]; exact fun _ h => h
  have args : ∀ σ s, Ctx L scr σ s → s.gpr .ebx = scr + BitVec.ofNat 32 oSt →
      InitArgs (H := h.H.st) s .ebx (scr + BitVec.ofNat 32 oSt) := fun σ s hc bx => by
    refine ⟨bx, by decide, ?_, ?_, ?_, fitS⟩
    · rw [hc.st.sp]; have := hc.st.ok.BC; have := hg.C48; omega
    · rw [hg.scrA (by decide), show h.H.st.S = h.N + h.B from hS]
      exact Covers.one (hg.wr hc.st (by unfold oSt oRsa; omega))
    · exact (((hg.low hc.st.ok (o := oSt) (n := h.N + h.B) (by unfold oSt oRsa; omega)).symm.sub_left
        (stk_low hg hc)).sub_right hsub)
  refine VP.of_ct (fun _ _ => init_rel h.ok.hH (sp := L.B) fun a b hab =>
    ⟨args _ _ hab.1.1 hab.1.2.2, args _ _ hab.2.1 hab.2.2.2, hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, bx⟩
  refine init_frame h.ok.hH (args σ s hc bx) fun s' af rp => ?_
  have fr : Frame [sR scr oSt (h.N + h.B), L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, hsub⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, stk_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) af.rd af.wr af.esp (af.cs .ebp (by simp [calleeSaved])), hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by unfold oSt oRsa; omega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · rw [hg.scrA (by decide)] at rp
    obtain ⟨e, -⟩ := h.ok.link.repr _ _ _ rp
    rw [e, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

end VG.Proof.RsaPss.X86
