import VerifiedGarbage.Proof.Ed448.Arm.Verify.Body
import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# Ed448 verification on ARMv7: constant time

As Ed25519's complete operations on this target, with the blocks and calls
of `Proof/Ed448/Arm/Shake/CT.lean`: two runs from the same pointers, lengths
and `sp` set up the same arguments for every call, each callee is constant
time under its own contract, and the blocks between the calls address
memory only through `sp`, `r12` and `scratch`. The positions the
absorptions return, which the next ones start from, depend only on the
lengths.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed448.Arm.Shake (firstArgs nextArgs absorb)
open VG.Proof.Ed25519.Arm (Whole.FR Whole.Within Whole.call_ok)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit argVal Two Slots valid_const valid_frame frame_within)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok scalarReduce_ct)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hash -/

/-- An absorption of input data at the position the previous one returned. -/
theorem input_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : valid 11 src) (vl : valid 11 len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argVal L.E L.value src), (argVal L.E L.value len).toNat⟩ R)
    (hfit : (argVal L.E L.value src).toNat + (argVal L.E L.value len).toNat ≤ 2 ^ 32) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC src len))
      (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value len).toNat) % 136)) :=
  hL.kit.next_ct ha hb (scr_at L) P hP vs vl (.inr ⟨R, List.mem_append_left _ hR, hw⟩)
    (hL.kit.data_input hR hw).1 hfit

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) Impl.Ed448.Arm.Verify.hash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  have hd' : argVal L.E L.value (.frame HDR) = L.E + BitVec.ofNat 32 HDR := rfl
  have hkn : (argVal L.E L.value (.const 10)).toNat = 10 := rfl
  have a1 := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) (src := .frame HDR) (len := .const 10)
    (valid_frame (by decide)) (valid_const (by decide))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact hk.frame_kWr (by decide))
    (by rw [hd', hkn]; exact hk.frame_fit (by decide))
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  have x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 1 0)
    (len := .caller 2 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 2 0)).toNat) % 136
  have x3 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.SIG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.ns; simp; omega)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 0 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega)
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x5 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  exact (hk.zeroState_ct ha hb (scr_at L)).seq (a1.seq (x2.seq (x3.seq (x4.seq (x5.seq
    ((hk.padStep_ct ha hb (scr_at L) P5 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (scr_at L) (by decide) (by decide))))))))

/-! ## The challenge and the equation -/

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  let args : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, scr 0)]
  have get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .frame K) (by simp [args])
    have h1 := hs.1 (.r1, .frame HASH) (by simp [args])
    have h2 := hs.1 (.r2, scr 0) (by simp [args])
    simp only [argVal, scr, SC, Lay.value, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  refine (hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, scr, SC, Slot, K, HASH])
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[hReg L], [kReg L, L.SCR], reduce_pre hL (get t h), reduce_covers L, reduce_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .frame K) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, scr 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL (get t hs)) (reduce_covers L)
      (reduce_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem equation_ct (hv : EqOk) (hct : EqCT) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith equationArgs "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)]
  have get : ∀ t, Slots L.E L.value args [] t → EqArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .caller 0 0) (by simp [args])
    have h1 := hs.1 (.r1, .caller 5 0) (by simp [args])
    have h2 := hs.1 (.r2, .frame K) (by simp [args])
    have h3 := hs.1 (.r3, scr 0) (by simp [args])
    simp only [argVal, scr, SC, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  refine (hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, scr, SC, Slot, K])
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct hv hct
    (fun t _ h => ⟨[L.PK, L.SIG, kReg L], [L.SCR], equation_pre hL (get t h), equation_covers L,
      equation_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hg (.r0, .caller 0 0) (by simp [args]), hg (.r1, .caller 5 0) (by simp [args]),
      hg (.r2, .frame K) (by simp [args]), hg (.r3, scr 0) (by simp [args]), hsp⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc hv equation_noFrames (equation_pre hL (get t hs)) (equation_covers L)
      (equation_writes L) fun v hv' _ _ => ⟨hv', trivial⟩

/-! ## The body -/

theorem body_ct (hv : EqOk) (hct : EqCT) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) body (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have h : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block hdr) (T2 L g₁ g₂ m₁ m₂ fun _ => True) :=
    (hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 2) (off := HDR) (by decide) hL.cl (by decide)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
  exact h.seq ((hash_ct hL ha hb).seq ((reduce_ct hL ha hb).seq (equation_ct hv hct hL ha hb)))

end VG.Proof.Ed448.Arm.Verify
