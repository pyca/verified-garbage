module

public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.SpecConv
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# `vg_gf25519_r32_pow250` and `vg_ed25519_r32_point_add` on PPC64LE, by register

Each function meets a contract of its facts by register (`powPPC`, `addPPC`),
with no stack (`pow_ok'`, `add_ok'`). The elements as the contracts read them
are the proofs' (`SpecConv`). No function writes a nonvolatile register or the
link register, or calls another.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- The working space of `pow250` and the point addition, `bytes` long, in `r3`. -/
def wsPre (bytes : Nat) (s : State) : Prop := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, bytes⟩]

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

/-- `pow250`'s facts by register: `a^(2^250 - 1)` and `a^11` from `a`, the rest of the
working space kept. -/
def powPPC : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .r3) s.mem s'.mem
  pub := wsPub

/-- The point addition's facts by register: `p + q` into `p`, the rest of the working space
kept. -/
def addPPC : Contract isa where
  pre s := wsPre 8192 s ∧ Proof.Ed25519.Point32.elemAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.dAt = Spec.Ed25519.d
  post s s' :=
    Proof.Ed25519.Point32.pointAt s'.mem (s.gpr .r3) Proof.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.pAt)
          (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.qAt) ∧
      Proof.Ed25519.Point32.Keeps (s.gpr .r3) s.mem s'.mem
  pub := wsPub

/-- Code that writes only the registers `R`, none of them nonvolatile, and never the link
register, keeps the ABI's registers. -/
theorem abi_of_rest {c : Prog isa} {R : List Reg} (hR : ∀ r ∈ preserved, r ∉ R) {s s' : State}
    {t : List Leak} (he : VG.Exec isa c s t s') (hr : Rest R s s') (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) : abiPreserved s s' :=
  ⟨fun r hr' => hr.gpr r (hR r hr'), hr.sp, Exec.lr he hn hl⟩

/-! ## `pow250` -/

theorem pow_ok' (s : State) (hs : powPPC.pre s) :
    ∃ t s', VG.Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powPPC.post s s' := by
  obtain ⟨_, hwr⟩ := hs
  obtain ⟨t, s', he, hR, hF, hE⟩ := pow250Fn_ok (s := s) rfl
    ⟨4096, Nat.le_refl _, by rw [hwr]; exact List.mem_singleton_self _⟩
  have h15 : env s'.mem (s.gpr .r3) 15 = Proof.X25519.pw (env s.mem (s.gpr .r3) 2) (2 ^ 250 - 1) := by
    rw [congrFun hE 15, (power250Env_eval _).1, Proof.X25519.chainF_eq]
  have h14 : env s'.mem (s.gpr .r3) 14 = Proof.X25519.pw (env s.mem (s.gpr .r3) 2) 11 := by
    rw [congrFun hE 14, (power250Env_eval _).2, Proof.X25519.chainF_eq]
  refine ⟨t, s', he, abi_of_rest (by decide) he hR (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), ?_, ?_, keeps_pow hF⟩
  · rw [show Proof.X25519.Field32.oAt = offset 15 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    have h := val_of_env h15
    exact h
  · rw [show Proof.X25519.Field32.eAt = offset 14 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    exact val_of_env (e := 11) h14

/-! ## The point addition -/

theorem addW_ok (b : Addr) :
    ∀ op ∈ pointAddOps, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ addW b, r.Sub r' := by
  have h : ∀ op ∈ pointAddOps, (opOut op).val < 4 ∨ (8 ≤ (opOut op).val ∧ (opOut op).val < 16) := by
    decide
  intro op hop r hr
  have ho := h op hop
  have hA := ACC_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases ho with ho | ho
    · exact ⟨_, List.mem_cons_self, Offset.sub _ (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        Offset.sub _ (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Offset.sub _ (Nat.le_refl _)
      (Nat.le_refl _)⟩

theorem add_ok' (s : State) (hs : addPPC.pre s) :
    ∃ t s', VG.Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addPPC.post s s' := by
  obtain ⟨⟨_, hwr⟩, hd⟩ := hs
  have hc : Ctx (s.gpr .r3) (s.write .r6 (s.gpr .r3 + BitVec.ofNat 64 0)) :=
    ⟨by simp [State.write], 8192, by decide, by simp [State.write, hwr]⟩
  have hw : WP isa addFn s fun t => Rest (.r6 :: clob) s t ∧ Frame (addW (s.gpr .r3)) s.mem t.mem ∧
      env t.mem (s.gpr .r3) = evalOps pointAddOps (env s.mem (s.gpr .r3)) := by
    refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
    have hc1 : Ctx (s.gpr .r3) s1 := ⟨by rw [u1.gpr]; simp, by rw [u1.wr, hwr]; exact ⟨8192, by decide, by simp⟩⟩
    refine WP.mono (fieldCodeW_ok pointAddOps (by decide) _ (addW_ok _) hc1) fun t ⟨hr, hf, he⟩ =>
      ⟨(u1.rest (by decide)).trans (hr.mono (by decide)), by rw [u1.mem] at hf; exact hf, by rw [he, u1.mem]⟩
  obtain ⟨t, s', he, hR, hF, hE⟩ := hw
  refine ⟨t, s', he, abi_of_rest (by decide) he hR (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), ?_, keeps_add hF⟩
  rw [pointAt_eq, pointAt_eq, pointAt_q, hE]
  exact pointAdd_eval _ (by rw [← elemAt_eq]; exact hd)

end VG.Proof.Ed25519.PPC64LE
