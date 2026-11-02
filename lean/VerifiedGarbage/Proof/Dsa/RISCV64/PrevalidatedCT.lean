module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA prevalidated verification on RISC-V: constant time

`vg_dsa_verify_prevalidated` (`Prevalidated.verify`) runs verification's
entry and, of the checks of the key, only the sizes, then sets up the working
spaces (`setupQ`, `setupP`) and runs `body`. Its levels are verification's
(`CTBase.lean`) up to the sizes' branch: their lists start with the same
programs, so their cuts' registers are verification's (`at_mono`,
`pins_mono`). The sizes' passing side `XR` is one level: cut at 0, 2 (after
`enterQ; ptrQ`) and 11 (after `enterP; ptrP`), then `body`'s levels from 26
(`body_rel'`), whose phase `SB` holds since the precondition makes the key
valid (`kv_of`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv at_step)
open VG.Proof.Bignum (slot)

/-! ## The levels -/

/-- On entry. -/
def C0p (v : VD) (s : State) : Prop := vpContract.pre s ∧ vdOf s = v

/-- After the sizes. -/
abbrev XR : Prog isa := .seq setupQ (.seq setupP Verify.body)
abbrev X2p : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs XR fail0)
abbrev X1p : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2p fail0)

abbrev FTp : List (Prog isa) := Code.flat Prevalidated.verify
abbrev FX1p : List (Prog isa) := Code.flat X1p
abbrev FX2p : List (Prog isa) := Code.flat X2p
abbrev FRp : List (Prog isa) := Code.flat XR

abbrev ΦX1p (v : VD) (u : State) : Prop := At C0p FTp 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2p (v : VD) (u : State) : Prop := At ΦX1p FX1p 5 v u ∧ u.gpr .a0 = 0
abbrev ΦRp (v : VD) (u : State) : Prop := At ΦX2p FX2p 12 v u ∧ u.gpr .a0 = 0

theorem hFTp : (FTp.drop 5).take 1 = [.ite (.zero .a0) X1p fail0] := rfl
theorem hFX1p : (FX1p.drop 5).take 1 = [.ite (.zero .a0) X2p fail0] := rfl
theorem hFX2p : (FX2p.drop 12).take 1 = [.ite (.zero .a0) XR fail0] := rfl

theorem runTp : ∀ v s, C0p v s → WP isa (Code.seqL FTp) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := prevalidated_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1p : ∀ v s, ΦX1p v s → WP isa (Code.seqL FX1p) s fun _ => True := run_then runTp hFTp
theorem runX2p : ∀ v s, ΦX2p v s → WP isa (Code.seqL FX2p) s fun _ => True := run_then runX1p hFX1p
theorem runRp : ∀ v s, ΦRp v s → WP isa (Code.seqL FRp) s fun _ => True := run_then runX2p hFX2p

theorem C0p.c0 {v : VD} {s : State} (h : C0p v s) : C0 v s := ⟨h.1.1, h.2⟩

/-- Each level's states are verification's. -/
theorem atT {n : Nat} (hn : FTp.take n = FT.take n) {v : VD} {u : State} (h : At C0p FTp n v u) : At C0 FT n v u :=
  at_mono (fun _ _ h => C0p.c0 h) hn h

theorem toX1 {v : VD} {u : State} (h : ΦX1p v u) : ΦX1 v u := ⟨atT rfl h.1, h.2⟩

theorem atX1 {n : Nat} (hn : FX1p.take n = FX1.take n) {v : VD} {u : State} (h : At ΦX1p FX1p n v u) :
    At ΦX1 FX1 n v u :=
  at_mono (fun _ _ h => toX1 h) hn h

theorem toX2 {v : VD} {u : State} (h : ΦX2p v u) : ΦX2 v u := ⟨atX1 rfl h.1, h.2⟩

theorem atX2 {n : Nat} (hn : FX2p.take n = FX2.take n) {v : VD} {u : State} (h : At ΦX2p FX2p n v u) :
    At ΦX2 FX2 n v u :=
  at_mono (fun _ _ h => toX2 h) hn h

theorem toR0 {v : VD} {u : State} (h : ΦRp v u) : ΦR0 v u := ⟨atX2 rfl h.1, h.2⟩

/-! ## The key is valid -/

/-- The key's public part passes the checks, on the public data. -/
abbrev KV (v : VD) : Prop := KM v ∧ EOk v (v.L.pl + v.L.ql) ∧ EOk v (2 * v.L.pl + v.L.ql)

theorem vd_bytes (s : State) {o k : Nat} (hk : o + k ≤ 3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat) :
    Spec.Rsa.bytesAt s.mem (off (s.gpr .a0) o) k = (vdOf s).sl o k := by
  rw [VD.sl, ← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a0) hk]; rfl

theorem kv_of {v : VD} {s : State} (h : C0p v s) : KV v := by
  obtain ⟨⟨hp, hval⟩, rfl⟩ := h
  have hv := hp.2.2.2.2.2.2.2.2.2.2.1
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hK : KeyOk s.mem (layOf s) (s.gpr .a0) := by
    have e := validate_spec (m := s.mem) (L := layOf s) (key := s.gpr .a0) hv
    rw [show 3 * (layOf s).pl + (layOf s).ql = (s.gpr .a1).toNat by simp only [layOf]; omega] at e
    exact of_decide_eq_true (e.symm.trans hval)
  have b0 := vd_bytes s (o := 0) (k := (s.gpr .a2).toNat) (by omega)
  rw [off, BitVec.add_zero] at b0
  have ep : pOf s.mem (layOf s) (s.gpr .a0) = (vdOf s).p := by rw [pOf]; exact congrArg _ b0
  have eq : qOf s.mem (layOf s) (s.gpr .a0) = (vdOf s).q := by rw [qOf]; exact congrArg _ (vd_bytes s (by simp only [layOf]; omega))
  have eg : gOf s.mem (layOf s) (s.gpr .a0) = (vdOf s).g := by rw [gOf]; exact congrArg _ (vd_bytes s (by simp only [layOf]; omega))
  have ey : yOf s.mem (layOf s) (s.gpr .a0) = (vdOf s).y := by rw [yOf]; exact congrArg _ (vd_bytes s (by simp only [layOf]; omega))
  rw [KeyOk, ep, eq, eg, ey] at hK
  obtain ⟨⟨hsz, hq, hp'⟩, ⟨⟨g1, g2⟩, ⟨y1, y2⟩⟩, hd, hg, hy⟩ := hK
  have bd := VG.Proof.Dsa.supported_bounds hsz
  exact ⟨⟨hsz, hp', hq, (pmod_iff (by omega) (by omega)).mp hd⟩, ⟨⟨g1, g2⟩, hg⟩, ⟨⟨y1, y2⟩, hy⟩⟩

theorem kvX1 {v : VD} {u : State} (h : ΦX1p v u) : KV v := at_pure (G := KV) (fun _ _ h => kv_of h) h.1
theorem kvX2 {v : VD} {u : State} (h : ΦX2p v u) : KV v := at_pure (G := KV) (fun _ _ h => kvX1 h) h.1
theorem kvR {v : VD} {u : State} (h : ΦRp v u) : KV v := at_pure (G := KV) (fun _ _ h => kvX2 h) h.1

/-! ## `XR` -/

theorem pinsRp_0 : Pins (At ΦRp FRp 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (semR0 (toR0 h)).1.fixB⟩

theorem pinsRp_2 : Pins (At ΦRp FRp 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key v.L.pl), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => by
    have B := (semR0 (toR0 h)).1
    refine WP.of_flat (c := .seq (.block enterQ) (.block ptrQ)) rfl
      (WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_))
    have B1 := B.keepM k m
    exact WP.mono (ptrQ_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
      ((B1.keepM k' m').fixB.app (fix_envQ (iq.keep k'))).app ⟨a7, a8, trivial⟩

/-- `setupQ`, after the sizes. -/
theorem setupQ_P1 {v : VD} {s : State} (h : P1 v s) (hk : KM v) :
    WP isa setupQ s fun t => SR3 v t := by
  obtain ⟨B, l, hsz⟩ := h
  refine WP.mono (setupQ_ok B.ok B.scr B.regs (B.hk.take (by omega))) fun t ⟨⟨_, q0, qtop, qb⟩, k⟩ => ?_
  have hb := qb.body B.ok
  exact ⟨⟨⟨B.body k hb, by rw [Lens, hb.word (by decide)]; exact l, hsz⟩, hk.2.1, hk.2.2.1⟩, hk.2.2.2,
    by rw [q0, B.q], qtop⟩

theorem pinsRp_11 : Pins (At ΦRp FRp 11) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq setupQ (.seq (.block enterP) (.block ptrP))) rfl
      (WP.seq (WP.mono (setupQ_P1 (semR0 (toR0 h)) (kvR h).1) fun _ hs => by
        have B := hs.1.1.1
        refine WP.seq (WP.mono (enterP_ok B.ok B.scr B.regs) fun _ ⟨⟨ip, m⟩, k⟩ => ?_)
        have B1 := B.keepM k m
        exact WP.mono (ptrP_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
          ((B1.keepM k' m').fixB.app (fix_envP (ip.keep k'))).app ⟨a7, a8, trivial⟩))

theorem semBp {v : VD} {u : State} (h : At ΦRp FRp 26 v u) : SB v u :=
  at_sem (M := SB) (fun _ _ h' => WP.of_flat (c := .seq setupQ setupP) rfl
    (WP.seq (WP.mono (setupQ_P1 (semR0 (toR0 h')) (kvR h').1) fun _ hs =>
      (setupP_SR3 hs).mono fun _ ⟨c, _⟩ => ⟨⟨c, (kvR h').1, (kvR h').2.1⟩, (kvR h').2.2⟩))) h

theorem drop26 : FRp.drop 26 = FB := by decide +kernel

theorem runBp : ∀ v s, At ΦRp FRp 26 v s → WP isa (Code.seqL FB) s fun _ => True := by
  intro v s h
  have h' := at_step runRp (m := 26 + FB.length) (Nat.le_add_right _ _) h
  have e : (FRp.drop 26).take (26 + FB.length - 26) = FB := by
    rw [drop26, Nat.add_sub_cancel_left, List.take_length]
  obtain ⟨t, u, ex, _⟩ := h'
  exact ⟨t, u, by rw [VG.Proof.Bignum.RISCV64.seg, e] at ex; exact ex, trivial⟩

theorem rel_flat {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True) :
    RelCT isa P (Code.seqL c.flat) fun _ _ => True :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)

theorem XR_rel : RelCT isa (Two ΦRp) XR fun _ _ => True := by
  refine chain_start (chain_cons runRp (m := 2) (by decide) (two_taint _ pinsRp_0 (by taint_decide)) ?_)
  refine chain_cons runRp (m := 11) (by decide) (two_taint _ pinsRp_2 (by taint_decide)) ?_
  refine chain_cons runRp (m := 26) (by decide) (two_taint _ pinsRp_11 (by taint_decide)) ?_
  rw [drop26]
  exact rel_flat (body_rel' runBp fun _ _ h => semBp h)

/-! ## The sizes' levels -/

theorem X2p_rel : RelCT isa (Two ΦX2p) X2p fun _ _ => True :=
  chain_start (chain_cons runX2p (m := 12) (by decide)
    (two_taint _ (pins_mono pinsX2_0 fun _ _ h => atX2 rfl h) (by taint_decide))
    (chain_cons runX2p (m := 13) (by decide) (rel_ite_at hFX2p
      (fun v s₁ s₂ h₁ h₂ => zeroX2 v s₁ s₂ (atX2 rfl h₁) (atX2 rfl h₂)) XR_rel fail_rel) nil_rel))

theorem X1p_rel : RelCT isa (Two ΦX1p) X1p fun _ _ => True := by
  refine chain_start (chain_cons runX1p (m := 2) (by decide)
    (two_taint _ (pins_mono pinsX1_0 fun _ _ h => atX1 rfl h) (by taint_decide)) ?_)
  refine chain_cons runX1p (m := 4) (by decide)
    (two_taint _ (pins_mono pinsX1_2 fun _ _ h => atX1 rfl h) (by taint_decide)) ?_
  refine chain_cons runX1p (m := 5) (by decide)
    (two_taint _ (pins_mono pinsX1_4 fun _ _ h => atX1 rfl h) (by taint_decide)) ?_
  exact chain_cons runX1p (m := 6) (by decide) (rel_ite_at hFX1p
    (fun v s₁ s₂ h₁ h₂ => zeroX1 v s₁ s₂ (atX1 rfl h₁) (atX1 rfl h₂)) X2p_rel fail_rel) nil_rel

theorem s6_keptp : ∀ i ∈ instrs (VG.Proof.Bignum.RISCV64.seg FTp 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (VG.Proof.Bignum.RISCV64.seg FTp 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTp6 : Pins (At C0p FTp 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [VG.Proof.Bignum.RISCV64.take_split FTp (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0p) (F := FTp) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Verify.entry) rfl (front_P0 h.c0)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptp e₂ rfl).trans h₁, trivial⟩

theorem prevalidated_rel : RelCT isa (Two C0p) Prevalidated.verify fun _ _ => True := by
  refine chain_start (chain_cons runTp (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (entry_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, (at_zero_inv h₁).c0, (at_zero_inv h₂).c0, hsp⟩) fun _ _ h => h
  refine chain_cons runTp (m := 2) (by decide) (two_taint _ (pins_mono pinsT1 fun _ _ h => atT rfl h)
    (by taint_decide)) ?_
  refine chain_cons runTp (m := 4) (by decide) (two_taint _ (pins_mono pinsT2 fun _ _ h => atT rfl h)
    (by taint_decide)) ?_
  refine chain_cons runTp (m := 5) (by decide) (two_taint _ (pins_mono pinsT4 fun _ _ h => atT rfl h)
    (by taint_decide)) ?_
  refine chain_cons runTp (m := 6) (by decide) (rel_ite_at hFTp
    (fun v s₁ s₂ h₁ h₂ => zeroT v s₁ s₂ (atT rfl h₁) (atT rfl h₂)) X1p_rel fail_rel) ?_
  exact two_taint _ pinsTp6 (by taint_decide)

theorem prevalidated_ct : ConstantTime isa vpContract.pre vpContract.pub Prevalidated.verify :=
  RelCT.constantTime (prevalidated_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdOf s, ⟨hs, rfl⟩, ⟨ht, (vdOf_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
