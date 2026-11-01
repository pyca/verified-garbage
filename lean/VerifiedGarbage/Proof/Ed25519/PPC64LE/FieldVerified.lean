module

public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.SpecConv
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

/-!
# `vg_gf25519_r32_mul`, `vg_gf25519_r32_pow250` and `vg_ed25519_r32_point_add` on PPC64LE, verified

Each function meets its contract of `Proof/X25519/Field32Contract.lean` or
`Proof/Ed25519/Point32Contract.lean`, with no stack: the proof against a contract of
its facts by register (`mulPPC`, `powPPC`, `addPPC`), which the shared one
implies, and a state satisfying it. The elements as the contracts read them
are the proofs' (`SpecConv`), and what a function keeps is its frame
(`keeps_mul`, `keeps_pow`, `keeps_add`). No function writes a nonvolatile
register or the link register, or calls another.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- An offset argument, the low word of its register. -/
abbrev offArg (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

/-- `mulContract` by register: `ws` in `r3`, `o`, `a` and `b` in `r4`–`r6`. -/
def mulPPC : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, 4096⟩] ∧ Fits (offArg s .r4) ∧ Fits (offArg s .r5) ∧
    Fits (offArg s .r6)
  post s s' := valAt s'.mem (s.gpr .r3) (offArg s .r4) % P =
      valAt s.mem (s.gpr .r3) (offArg s .r5) * valAt s.mem (s.gpr .r3) (offArg s .r6) % P ∧
    Keeps (s.gpr .r3) (offArg s .r4) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ offArg s₁ .r4 = offArg s₂ .r4 ∧ offArg s₁ .r5 = offArg s₂ .r5 ∧
    offArg s₁ .r6 = offArg s₂ .r6 ∧ s₁.sp = s₂.sp

/-- The working space of `pow250` and the point addition, `bytes` long, in `r3`. -/
def wsPre (bytes : Nat) (s : State) : Prop := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, bytes⟩]

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

/-- `pow250Contract` by register. -/
def powPPC : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .r3) s.mem s'.mem
  pub := wsPub

/-- `addContract` by register. -/
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

/-- A state satisfying the preconditions of `mul` and `pow250`: `ws` at `0x1000`, every offset
0. -/
def satWs : State where
  gpr r := match r with | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 4096⟩]

/-! ## `mul` -/

theorem fits_toNat {s : State} {r : Reg} (h : Fits (offArg s r)) :
    (s.gpr r).toNat % 2 ^ 32 = (offArg s r).toNat ∧ (offArg s r).toNat + 32 ≤ 768 := by
  refine ⟨by rw [BitVec.toNat_setWidth], ?_⟩
  simpa [Fits, Proof.X25519.Field32.elemBytes, Proof.X25519.Field32.ownAt] using h

theorem mul_ok' (s : State) (hs : mulPPC.pre s) :
    ∃ t s', VG.Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulPPC.post s s' := by
  obtain ⟨_, hwr, f4, f5, f6⟩ := hs
  obtain ⟨e4, h4⟩ := fits_toNat f4
  obtain ⟨e5, h5⟩ := fits_toNat f5
  obtain ⟨e6, h6⟩ := fits_toNat f6
  have hc : Ctx3 (s.gpr .r3) s := ⟨rfl, 4096, Nat.le_refl _, by rw [hwr]; exact List.mem_singleton_self _⟩
  obtain ⟨t, s', he, hR, hF, hV⟩ := mulFn_ok h4 h5 h6 hc e4 e5 e6
  refine ⟨t, s', he, mulFn_abi he hR, ?_, keeps_mul h4 hF⟩
  rw [valAt_eq, valAt_eq, valAt_eq]; exact hV

theorem mulFn_verified : Verified PPC64LE.target mulFn (Proof.X25519.Field32.mulContract PPC64LE.abi) :=
  Verified.of_correct mul_ok' (mulFn_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, h3, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.X25519.Field32.mulContract, Proof.X25519.Field32.sig, mulPPC, offArg,
      PPC64LE.abi, PPC64LE.argRegs] [satWs] using satWs)

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

theorem pow250Fn_verified : Verified PPC64LE.target pow250Fn (Proof.X25519.Field32.pow250Contract PPC64LE.abi) :=
  Verified.of_correct pow_ok' (pow250Fn_ct fun _ _ _ _ ⟨h3, hsp⟩ => ⟨hsp, h3⟩) (by
    contract_implies [Proof.X25519.Field32.pow250Contract, Proof.X25519.Field32.pow250Sig, powPPC, wsPre, wsPub,
      PPC64LE.abi, PPC64LE.argRegs] [satWs] using satWs)

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

/-- `d`'s value. -/
def dLit : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The working space at `0x1000`, holding `d` in slot 16. -/
def addMem : Mem := fun a =>
  if 0x1240 ≤ a.toNat ∧ a.toNat < 0x1260 then BitVec.ofNat 8 (dLit / 256 ^ (a.toNat - 0x1240)) else 0

/-- A state satisfying the point addition's precondition. -/
def satAdd : State where
  gpr r := match r with | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := addMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem addMem_d : (addMem.read ((0x1000 : Addr) + BitVec.ofNat 64 576) 32).toNat = dLit := by
  decide +kernel

theorem d_eq : Spec.Ed25519.d = Fin.ofNat Spec.X25519.P dLit := by decide +kernel

theorem satAdd_d :
    Proof.Ed25519.Point32.elemAt satAdd.mem (0x1000 : Addr) Proof.Ed25519.Point32.dAt = Spec.Ed25519.d := by
  rw [d_eq, Proof.Ed25519.Point32.elemAt]
  exact congrArg _ addMem_d

theorem addFn_verified : Verified PPC64LE.target addFn (Proof.Ed25519.Point32.addContract PPC64LE.abi) :=
  Verified.of_correct add_ok' (addFn_ct fun _ _ _ _ ⟨h3, hsp⟩ => ⟨hsp, h3⟩)
    { pre := by implies_pre [Proof.Ed25519.Point32.addContract, Proof.Ed25519.Point32.sig, addPPC, wsPre, wsPub,
        PPC64LE.abi, PPC64LE.argRegs]
      post := by implies_post [Proof.Ed25519.Point32.addContract, Proof.Ed25519.Point32.sig, addPPC, wsPre, wsPub,
        PPC64LE.abi, PPC64LE.argRegs]
      pub := by implies_pub [Proof.Ed25519.Point32.addContract, Proof.Ed25519.Point32.sig, addPPC, wsPre, wsPub,
        PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        refine ⟨satAdd, ?_⟩
        sig_pre [Proof.Ed25519.Point32.addContract, Proof.Ed25519.Point32.sig, addPPC, wsPre, PPC64LE.abi,
          PPC64LE.argRegs, satAdd]
        sig_and_intros
        all_goals first
          | exact satAdd_d
          | rfl
          | decide }

end VG.Proof.Ed25519.PPC64LE
