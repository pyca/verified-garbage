module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCTB
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCTB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedCT
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation for a checked domain on RISC-V: constant time

`vg_dsa_derive_key_checked` (`Generate.deriveChecked`) runs `Derive.entry`,
then of the checks of the domain only the sizes, then sets up the working
spaces (`setupQ`, `setupP`) and runs `Derive.body`, else `zeroOut`, then
`restore`. Its public data is `vg_dsa_derive_key`'s (`vdD`). Its levels are
derivation's (`DeriveCT.lean`) up to the sizes' branch: their lists start
with the same programs (`atL`, `pinsL`, `zeroL`). The sizes' passing side
`XRdc` is one level, as prevalidated verification's (`PrevalidatedCT.lean`):
cut at 0, 2 (after `enterQ; ptrQ`) and 11 (after `enterP; ptrP`), then
`body`'s levels from 26 (`body_relD`), whose phase `DB` holds since the
precondition makes the domain valid (`kd_of`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv at_step take_split)

/-! ## The levels -/

/-- On entry. -/
def C0dc (v : VD) (s : State) : Prop := dcContract.pre s ∧ vdD s = v

theorem C0dc.c0d {v : VD} {s : State} (h : C0dc v s) : C0d v s := ⟨h.1.1, h.2⟩

theorem frontDc : ∀ v s, C0dc v s → WP isa (.block Derive.entry) s (P0 v) := fun _ _ h => frontD _ _ h.c0d

/-- After the sizes. -/
abbrev XRdc : Prog isa := .seq setupQ (.seq setupP Derive.body)
abbrev X2dc : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs XRdc Derive.zeroOut)
abbrev X1dc : Prog isa :=
  .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2dc Derive.zeroOut)

abbrev FTdc : List (Prog isa) := Code.flat Generate.deriveChecked
abbrev FX1dc : List (Prog isa) := Code.flat X1dc
abbrev FX2dc : List (Prog isa) := Code.flat X2dc
abbrev FRdc : List (Prog isa) := Code.flat XRdc

abbrev ΦX1dc (v : VD) (u : State) : Prop := At C0dc FTdc 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2dc (v : VD) (u : State) : Prop := At ΦX1dc FX1dc 5 v u ∧ u.gpr .a0 = 0
abbrev ΦRdc (v : VD) (u : State) : Prop := At ΦX2dc FX2dc 12 v u ∧ u.gpr .a0 = 0

theorem hFTdc : (FTdc.drop 5).take 1 = [.ite (.zero .a0) X1dc Derive.zeroOut] := rfl
theorem hFX1dc : (FX1dc.drop 5).take 1 = [.ite (.zero .a0) X2dc Derive.zeroOut] := rfl
theorem hFX2dc : (FX2dc.drop 12).take 1 = [.ite (.zero .a0) XRdc Derive.zeroOut] := rfl

theorem runTdc : ∀ v s, C0dc v s → WP isa (Code.seqL FTdc) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := deriveChecked_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1dc : ∀ v s, ΦX1dc v s → WP isa (Code.seqL FX1dc) s fun _ => True := run_then runTdc hFTdc
theorem runX2dc : ∀ v s, ΦX2dc v s → WP isa (Code.seqL FX2dc) s fun _ => True := run_then runX1dc hFX1dc
theorem runRdc : ∀ v s, ΦRdc v s → WP isa (Code.seqL FRdc) s fun _ => True := run_then runX2dc hFX2dc

theorem onX1dc : ∀ v u, ΦX1dc v u → SX1 v u := fun _ _ h => semX1 frontDc ⟨atL rfl h.1, h.2⟩
theorem onX2dc : ∀ v u, ΦX2dc v u → SX2 v u := fun _ _ h => semX2 onX1dc ⟨atL rfl h.1, h.2⟩
theorem onRdc : ∀ v u, ΦRdc v u → P1 v u := fun _ _ h => semR0 onX2dc ⟨atL rfl h.1, h.2⟩

theorem outDc : ∀ v s, C0dc v s → v.out = some (oOf v) := fun _ _ h => outD _ _ h.c0d
theorem oX1dc : ∀ v u, ΦX1dc v u → v.out = some (oOf v) := fun _ _ h => at_pure outDc h.1
theorem oX2dc : ∀ v u, ΦX2dc v u → v.out = some (oOf v) := fun _ _ h => at_pure oX1dc h.1

/-! ## The domain is valid -/

/-- The domain passes the checks, on the public data. -/
abbrev KD (v : VD) : Prop := KM v ∧ EOk v (v.L.pl + v.L.ql)

theorem vdD_bytes (s : State) {o k : Nat} (hk : o + k ≤ (s.gpr .a3).toNat) :
    Spec.Rsa.bytesAt s.mem (off (s.gpr .a2) o) k = (vdD s).sl o k := by
  rw [VD.sl, ← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a2) hk]; rfl

theorem kd_of {v : VD} {s : State} (h : C0dc v s) : KD v := by
  obtain ⟨hc, rfl⟩ := h
  have hP := dcParams hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpl, -, -, -⟩ := hc.1
  have b0 := vdD_bytes s (o := 0) (k := (s.gpr .a4).toNat) (by omega)
  rw [off, BitVec.add_zero] at b0
  have ep : pOf s.mem (dlayOf s) (s.gpr .a2) = (vdD s).p := by rw [pOf]; exact congrArg _ b0
  have eq : qOf s.mem (dlayOf s) (s.gpr .a2) = (vdD s).q := by
    rw [qOf]; exact congrArg _ (vdD_bytes s (by simp only [dlayOf]; omega))
  have eg : gOf s.mem (dlayOf s) (s.gpr .a2) = (vdD s).g := by
    rw [gOf]; exact congrArg _ (vdD_bytes s (by simp only [dlayOf]; omega))
  rw [ParamsOk, ep, eq, eg] at hP
  obtain ⟨⟨hsz, hq, hp'⟩, ⟨g1, g2⟩, hd, hg⟩ := hP
  have bd := VG.Proof.Dsa.supported_bounds hsz
  exact ⟨⟨hsz, hp', hq, (pmod_iff (by omega) (by omega)).mp hd⟩, ⟨g1, g2⟩, hg⟩

theorem kdcX1 {v : VD} {u : State} (h : ΦX1dc v u) : KD v := at_pure (G := KD) (fun _ _ h => kd_of h) h.1
theorem kdcX2 {v : VD} {u : State} (h : ΦX2dc v u) : KD v := at_pure (G := KD) (fun _ _ h => kdcX1 h) h.1
theorem kdcR {v : VD} {u : State} (h : ΦRdc v u) : KD v := at_pure (G := KD) (fun _ _ h => kdcX2 h) h.1

theorem gRdc {v : VD} {u : State} (h : ΦRdc v u) : GD v :=
  at_pure (G := GD) (fun _ _ h => at_pure (G := GD) (fun _ _ h =>
    at_pure (G := GD) (fun _ _ h => gC0d _ _ h.c0d) h.1) h.1) h.1

theorem owRdc : ∀ v u, ΦRdc v u → OW v u := fun _ _ h =>
  ow_at (o := id) (fun _ _ h => ow_at (o := id) (fun _ _ h =>
    ow_at (o := id) (fun _ _ h => owC0d _ _ h.c0d) h.1) h.1) h.1

/-! ## `XRdc` -/

theorem pinsRdc_0 : Pins (At ΦRdc FRdc 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (onRdc _ _ h).1.fixB⟩

theorem pinsRdc_2 : Pins (At ΦRdc FRdc 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key v.L.pl), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => by
    have B := (onRdc _ _ h).1
    refine WP.of_flat (c := .seq (.block enterQ) (.block ptrQ)) rfl
      (WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_))
    have B1 := B.keepM k m
    exact WP.mono (ptrQ_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
      ((B1.keepM k' m').fixB.app (fix_envQ (iq.keep k'))).app ⟨a7, a8, trivial⟩

theorem pinsRdc_11 : Pins (At ΦRdc FRdc 11) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq setupQ (.seq (.block enterP) (.block ptrP))) rfl
      (WP.seq (WP.mono (setupQ_P1 (onRdc _ _ h) (kdcR h).1) fun _ hs => by
        have B := hs.1.1.1
        refine WP.seq (WP.mono (enterP_ok B.ok B.scr B.regs) fun _ ⟨⟨ip, m⟩, k⟩ => ?_)
        have B1 := B.keepM k m
        exact WP.mono (ptrP_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
          ((B1.keepM k' m').fixB.app (fix_envP (ip.keep k'))).app ⟨a7, a8, trivial⟩))

theorem semBdc {v : VD} {u : State} (h : At ΦRdc FRdc 26 v u) : DB v u :=
  ⟨at_sem (M := SD) (fun _ _ h' => WP.of_flat (c := .seq setupQ setupP) rfl
    (WP.seq (WP.mono (setupQ_P1 (onRdc _ _ h') (kdcR h').1) fun _ hs =>
      (setupP_SR3 hs).mono fun _ ⟨c, _⟩ => ⟨c, (kdcR h').1, (kdcR h').2⟩))) h,
    at_pure (G := GD) (fun _ _ h => gRdc h) h, ow_at (o := id) owRdc h⟩

theorem drop26dc : FRdc.drop 26 = FBd := by decide +kernel

theorem runBdc : ∀ v s, At ΦRdc FRdc 26 v s → WP isa (Code.seqL FBd) s fun _ => True := by
  intro v s h
  have h' := at_step runRdc (m := 26 + FBd.length) (Nat.le_add_right _ _) h
  have e : (FRdc.drop 26).take (26 + FBd.length - 26) = FBd := by
    rw [drop26dc, Nat.add_sub_cancel_left, List.take_length]
  obtain ⟨t, u, ex, _⟩ := h'
  exact ⟨t, u, by rw [VG.Proof.Bignum.RISCV64.seg, e] at ex; exact ex, trivial⟩

theorem XRdc_rel : RelCT isa (Two ΦRdc) XRdc fun _ _ => True := by
  refine chain_start (chain_cons runRdc (m := 2) (by decide) (two_taint _ pinsRdc_0 (by taint_decide)) ?_)
  refine chain_cons runRdc (m := 11) (by decide) (two_taint _ pinsRdc_2 (by taint_decide)) ?_
  refine chain_cons runRdc (m := 26) (by decide) (two_taint _ pinsRdc_11 (by taint_decide)) ?_
  rw [drop26dc]
  exact rel_flat (body_relD runBdc fun _ _ h => semBdc h)

/-! ## The sizes' levels -/

theorem X2dc_rel : RelCT isa (Two ΦX2dc) X2dc fun _ _ => True :=
  chain_start (chain_cons runX2dc (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2dc)) (by taint_decide))
    (chain_cons runX2dc (m := 13) (by decide) (rel_ite_at hFX2dc (zeroL rfl (zeroX2 onX2dc)) XRdc_rel
      (zero_rel (run_else runX2dc hFX2dc)
        (fun _ _ h => (at_sem (Φ := ΦX2dc) (F := FX2) (n := 12) (M := MX2) (fun _ _ h => midX2 onX2dc h)
          (atL rfl h.1)).1)
        fun _ _ h => at_pure oX2dc h.1)) nil_rel))

theorem X1dc_rel : RelCT isa (Two ΦX1dc) X1dc fun _ _ => True := by
  refine chain_start (chain_cons runX1dc (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1dc)) (by taint_decide)) ?_)
  refine chain_cons runX1dc (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1dc)) (by taint_decide)) ?_
  refine chain_cons runX1dc (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1dc)) (by taint_decide)) ?_
  exact chain_cons runX1dc (m := 6) (by decide) (rel_ite_at hFX1dc (zeroL rfl (zeroX1 onX1dc)) X2dc_rel
    (zero_rel (run_else runX1dc hFX1dc)
      (fun _ _ h => (at_sem (Φ := ΦX1dc) (F := FX1) (n := 5) (M := MX1) (fun _ _ h => midX1 onX1dc h)
        (atL rfl h.1)).1.1)
      fun _ _ h => at_pure oX1dc h.1)) nil_rel

/-! ## The function -/

/-- `scratch` is public. -/
theorem pins_a7dc : Pins C0dc [.a7] := fun v _ _ h₁ h₂ r hr => pins_a7 v _ _ h₁.c0d h₂.c0d r hr

theorem s6_keptdc : ∀ i ∈ instrs (seg FTdc 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTdc 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTdc6 : Pins (At C0dc FTdc 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTdc (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0dc) (F := FTdc) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Derive.entry) rfl (frontDc _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptdc e₂ rfl).trans h₁, trivial⟩

theorem deriveChecked_rel : RelCT isa (Two C0dc) Generate.deriveChecked fun _ _ => True := by
  refine chain_start (chain_cons runTdc (m := 1) (by decide)
    (two_taint _ (pins_mono pins_a7dc fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTdc (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontDc)) (by taint_decide)) ?_
  refine chain_cons runTdc (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontDc)) (by taint_decide)) ?_
  refine chain_cons runTdc (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontDc)) (by taint_decide)) ?_
  refine chain_cons runTdc (m := 6) (by decide) (rel_ite_at hFTdc (zeroL rfl (zeroT frontDc)) X1dc_rel
    (zero_rel (run_else runTdc hFTdc) (fun _ _ h => (at_sem (Φ := C0dc) (F := TF Derive.entry) (n := 5) (M := MT)
        (fun _ _ h => midT frontDc h) (atL rfl h.1)).1.1)
      fun _ _ h => at_pure outDc h.1)) ?_
  exact two_taint _ pinsTdc6 (by taint_decide)

theorem deriveChecked_ct : ConstantTime isa dcContract.pre dcContract.pub Generate.deriveChecked :=
  RelCT.constantTime (deriveChecked_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdD s, ⟨hs, rfl⟩, ⟨ht, (vdD_eq hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
