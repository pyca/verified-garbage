module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the taint checks of its levels cost more than their imports, and the registration
-- states the result without them

/-!
# DSA private-key validation on RISC-V: constant time

`vg_dsa_validate_private_key` (`PrevalidatedSign.validate`) runs
`vg_dsa_validate_public_key`'s entry, then `checkSignKey`'s checks of the
domain and of y's range, then `keyPair; xRange` (`VR`). Its public data
(`vdV`) are the key's public octets p||q||g||y (not x), and `scratch`. Its
levels up to y's range are validation's (`ValidateCT.lean`), but the key's
level has no `elemOrder`, as signing's (`SignCT.lean`). `VR` is cut as
signing's body is in `keyPair` (2, 12, 53), then after it (64), after
`enterQ` (65) and after `ptrX` (69); between them the phase `VK` carries the
P space's facts and x's region. Nothing branches on x: the result is the
mask's low bit.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv take_split)
open VG.Proof.Bignum (slot)

/-! ## The entry -/

/-- A call's public data: the key's public octets. -/
def vdV (s : State) : VD :=
  ⟨playOf s, s.gpr .a0, 0, 0, 0, Spec.Rsa.bytesAt s.mem (s.gpr .a0) (3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat),
    3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat, 0, false, none⟩

/-- On entry. -/
def C0v (v : VD) (s : State) : Prop := vpkContract.pre s ∧ vdV s = v

theorem frontV : ∀ v s, C0v v s → WP isa (.block Params.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  have hL : (playOf s).Ok := playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
  have hZ := hL.z256
  obtain ⟨hrd, hwr, dKS, -, nw, -, hkl, -, alS, -⟩ := h
  refine WP.mono (pfront_ok_of hL hwr nw alS) fun t ⟨F, k⟩ => ?_
  have hK : Src t (playOf s) (s.gpr .a0) (3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat) :=
    psrc_of hrd dKS (by omega) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, src_nil rfl, src_nil (Nat.zero_min _),
    hK.bytes F.out (by simp only [playOf] at hZ ⊢; omega), (by simp only [vdV, playOf]; omega),
    (fun h => nomatch h), fun _ h => nomatch h⟩, F.lens.trans (congrArg _ (Nat.zero_min _).symm)⟩

theorem kyC0v : ∀ v s, C0v v s → KY v := by
  rintro _ s ⟨-, rfl⟩
  exact Nat.le_refl _

/-- x's octets, with the key's, may be read, apart from `scratch`. -/
abbrev XS (v : VD) (u : State) : Prop := Src u v.L v.key (3 * v.L.pl + 2 * v.L.ql)

theorem xsC0v : ∀ v s, C0v v s → XS v s := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨hrd, -, dKS, -, -, -, hkl, -⟩ := h
  exact psrc_of hrd dKS (by simp only [vdV, playOf]; omega) rfl rfl

theorem xs_at {Φ : VD → State → Prop} {F : List (Prog isa)} {n : Nat} (h : ∀ v s, Φ v s → XS v s) {v : VD}
    {u : State} (hu : At Φ F n v u) : XS v u := by
  obtain ⟨s₀, t, h₀, e⟩ := hu
  obtain ⟨hr, hw, -⟩ := Exec.rdwr e
  exact (h v s₀ h₀).keep hr hw

/-! ## The levels -/

abbrev VR : Prog isa := .seq Sign.keyPair PrevalidatedSign.xRange
abbrev RKv : Prog isa := andThen (.seq (.block ptrY) (.seq (loadArr 4) elemRange)) VR fail0
abbrev R3v : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) RKv fail0)
abbrev R2v : Prog isa := andThen pModQ R3v fail0
abbrev R1v : Prog isa := andThen (.block (ptrQ ++ odd)) R2v fail0
abbrev R0v : Prog isa := odds R2v fail0
abbrev X2v : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0v fail0)
abbrev X1v : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2v fail0)

abbrev FTv : List (Prog isa) := Code.flat PrevalidatedSign.validate
abbrev FX1v : List (Prog isa) := Code.flat X1v
abbrev FX2v : List (Prog isa) := Code.flat X2v
abbrev FR0v : List (Prog isa) := Code.flat R0v
abbrev FR1v : List (Prog isa) := Code.flat R1v
abbrev FR2v : List (Prog isa) := Code.flat R2v
abbrev FR3v : List (Prog isa) := Code.flat R3v
abbrev FKv : List (Prog isa) := Code.flat RKv
abbrev FVR : List (Prog isa) := Code.flat VR

abbrev ΦX1v (v : VD) (u : State) : Prop := At C0v FTv 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2v (v : VD) (u : State) : Prop := At ΦX1v FX1v 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0v (v : VD) (u : State) : Prop := At ΦX2v FX2v 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1v (v : VD) (u : State) : Prop := At ΦR0v FR0v 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2v (v : VD) (u : State) : Prop := At ΦR1v FR1v 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3v (v : VD) (u : State) : Prop := At ΦR2v FR2v 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgv (v : VD) (u : State) : Prop := At ΦR3v FR3v 45 v u ∧ u.gpr .a0 = 0
abbrev ΦKv (v : VD) (u : State) : Prop := At ΦR3v FR3v 46 v u ∧ u.gpr .a0 = 0
abbrev ΦVR (v : VD) (u : State) : Prop := At ΦKv FKv 28 v u ∧ u.gpr .a0 = 0

theorem hFTv : (FTv.drop 5).take 1 = [.ite (.zero .a0) X1v fail0] := rfl
theorem hFX1v : (FX1v.drop 5).take 1 = [.ite (.zero .a0) X2v fail0] := rfl
theorem hFX2v : (FX2v.drop 12).take 1 = [.ite (.zero .a0) R0v fail0] := rfl
theorem hFR0v : (FR0v.drop 1).take 1 = [.ite (.zero .a0) R1v fail0] := rfl
theorem hFR1v : (FR1v.drop 1).take 1 = [.ite (.zero .a0) R2v fail0] := rfl
theorem hFR2v : (FR2v.drop 23).take 1 = [.ite (.zero .a0) R3v fail0] := rfl
theorem hFR3gv : (FR3v.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3v : (FR3v.drop 46).take 1 = [.ite (.zero .a0) RKv fail0] := rfl
theorem hFKv : (FKv.drop 28).take 1 = [.ite (.zero .a0) VR fail0] := rfl

theorem runTv : ∀ v s, C0v v s → WP isa (Code.seqL FTv) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := validatePriv_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1v : ∀ v s, ΦX1v v s → WP isa (Code.seqL FX1v) s fun _ => True := run_then runTv hFTv
theorem runX2v : ∀ v s, ΦX2v v s → WP isa (Code.seqL FX2v) s fun _ => True := run_then runX1v hFX1v
theorem runR0v : ∀ v s, ΦR0v v s → WP isa (Code.seqL FR0v) s fun _ => True := run_then runX2v hFX2v
theorem runR1v : ∀ v s, ΦR1v v s → WP isa (Code.seqL FR1v) s fun _ => True := run_then runR0v hFR0v
theorem runR2v : ∀ v s, ΦR2v v s → WP isa (Code.seqL FR2v) s fun _ => True := run_then runR1v hFR1v
theorem runR3v : ∀ v s, ΦR3v v s → WP isa (Code.seqL FR3v) s fun _ => True := run_then runR2v hFR2v
theorem runEgv : ∀ v s, ΦEgv v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3v hFR3gv
theorem runKv : ∀ v s, ΦKv v s → WP isa (Code.seqL FKv) s fun _ => True := run_then runR3v hFR3v
theorem runVR : ∀ v s, ΦVR v s → WP isa (Code.seqL FVR) s fun _ => True := run_then runKv hFKv

theorem onX1v : ∀ v u, ΦX1v v u → SX1 v u := fun _ _ h => semX1 frontV ⟨atL rfl h.1, h.2⟩
theorem onX2v : ∀ v u, ΦX2v v u → SX2 v u := fun _ _ h => semX2 onX1v ⟨atL rfl h.1, h.2⟩
theorem onR0v : ∀ v u, ΦR0v v u → P1 v u := fun _ _ h => semR0 onX2v ⟨atL rfl h.1, h.2⟩
theorem onR1v : ∀ v u, ΦR1v v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0v ⟨atL rfl h.1, h.2⟩
theorem onR2v : ∀ v u, ΦR2v v u → SR2 v u := fun _ _ h => semR2 onR1v ⟨atL rfl h.1, h.2⟩
theorem onR3v : ∀ v u, ΦR3v v u → SR3 v u := fun _ _ h => semR3 onR2v ⟨atL rfl h.1, h.2⟩

theorem kyR3v : ∀ v u, ΦR3v v u → KY v := fun _ _ h =>
  at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h =>
    at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) kyC0v h.1) h.1) h.1) h.1)
      h.1) h.1

theorem xsKv : ∀ v u, ΦKv v u → XS v u := fun _ _ h =>
  xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h =>
    xs_at (fun _ _ h => xs_at xsC0v h.1) h.1) h.1) h.1) h.1) h.1) h.1

theorem onKv : ∀ v u, ΦKv v u → SK v u := fun _ _ h => semK onR3v kyR3v ⟨atL rfl h.1, h.2⟩

theorem midKv {v : VD} {s : State} (h : ΦKv v s) : WP isa (Code.seqL (FKv.take 28)) s (MKs v) := by
  obtain ⟨c, km, eg, ky⟩ := onKv _ _ h
  exact WP.of_flat (c := .seq (.block ptrY) (.seq (loadArr 4) elemRange)) rfl
    (WP.seq ((ptr_CK c (ptrY_ok c.base.scr c.base.ok c.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ =>
      (yrange_CK c' (by omega) a7 a8).mono fun _ ⟨c'', a0⟩ => ⟨⟨c'', km, eg, ky⟩, a0⟩))

theorem zeroKv : ∀ v s₁ s₂, At ΦKv FKv 28 v s₁ → At ΦKv FKv 28 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => ERange v (2 * v.L.pl + v.L.ql)) fun _ _ h => (midKv h).mono fun _ h => h.2

/-! ## `VR` -/

/-- `VR`'s phase: the P space as the checks leave it, q in the Q space's array
0, and x's region. -/
structure VK (v : VD) (t : State) : Prop where
  cb : CB v t
  q0 : arrQ t.mem v.L 0 = v.q
  xs : XS v t

theorem VK.keepM {v : VD} {s t : State} {rs : List Reg} (h : VK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs ++ ([.t1] : List Reg), r ∉ rs := by decide) : VK v t :=
  ⟨⟨h.cb.1.keepM k hm fun r hm' => hr r (by simp [hm']),
    h.cb.2.1.keep k fun r hm' => hr r (by simp [hm']),
    by show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
       rw [hm, k.gpr (fun hm' => hr .t1 (by simp) hm')]; exact h.cb.2.2.1,
    by rw [arrP, hm]; exact h.cb.2.2.2.1, by rw [arrP, hm]; exact h.cb.2.2.2.2⟩,
    by rw [arrQ, hm]; exact h.q0, h.xs.keep k.2.1 k.2.2⟩

/-- `VR`'s states are in its phase. -/
theorem onVR {v : VD} {u : State} (h : ΦVR v u) : VK v u ∧ KM v := by
  have m := at_sem (Φ := ΦKv) (F := FKv) (n := 28) (M := MKs) (fun _ _ h => midKv h) h.1
  obtain ⟨⟨c, km, -⟩, -⟩ := m
  exact ⟨⟨⟨c.base, c.inp, c.inv, c.p0, c.p24⟩, c.q0, xs_at xsKv h.1⟩, km⟩

/-- `keyPair`'s first block: x's and g's pointers. -/
theorem stKV0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : VK v s)
    (hc : ∀ t, VK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) → WP isa c t Q) :
    WP isa (.seq (.block KP0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (ptrX_ok B.scr hL B.regs) fun s₁ ⟨⟨a7, _, m1⟩, k1⟩ =>
    WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧ u.mem = s₁.mem)
      (by brun [a7, BitVec.add_zero]) (by decide) (by rfl)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)))
  have h2 := (h.keepM k1 m1).keepM k2 m2
  exact WP.mono (ptrG_ok h2.cb.1.scr hL h2.cb.1.regs) fun t ⟨⟨b7, b8, m3⟩, k3⟩ =>
    hc t (h2.keepM k3 m3) b7 b8 ((k3.gpr (by decide)).trans a9)

theorem pinsV0 : Pins (At ΦVR FVR 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, fix_CB (onVR h).1.cb⟩

theorem pinsV2 : Pins (At ΦVR FVR 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.key (3 * v.L.pl + v.L.ql))]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.block (getP .s8))) (by decide +kernel)
      (stKV0 (onVR h).1 fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_CB (c.keepM k m).cb).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsV12 : Pins (At ΦVR FVR 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
      (.block (getQ .s10)))))) (by decide +kernel)
      (stKV0 (onVR h).1 fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 a9)

/-- A power in the P space, from its pointers. -/
theorem powV {v : VD} {s : State} {N E : Addr} (h : VK v s) (hN : Src s v.L N v.L.pl) (h7 : s.gpr .s7 = N)
    (hE : Src s v.L E v.L.ql) (h9 : s.gpr .s9 = E) (hp : 2 ≤ v.p) (hpo : v.p % 2 = 1) :
    WP isa Verify.powP s fun t => VK v t := by
  have B := h.cb.1; have ip := h.cb.2.1; have I := h.cb.2.2.1; have p0 := h.cb.2.2.2.1
  have p24 := h.cb.2.2.2.2
  have hL := B.ok
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have hw := hL.wp_ge
  refine WP.mono (powSrc_ok hL B.scr B.regs ip I hN h7 hE h9 p0 hp hpo p24) fun t ⟨⟨_, ip', I', o⟩, k⟩ => ?_
  have hb := p_arrays_body hL o
  exact ⟨⟨B.body k hb, ip', I', (o.wordsVal (by omega) (by omega_arith)).trans p0,
    (o.wordsVal (by omega) (by omega_arith)).trans p24⟩, (keepQ_arr0 hL (PLow.keepQ hL o)).trans h.q0,
    h.xs.keep k.2.1 k.2.2⟩

theorem pinsV53 : Pins (At ΦVR FVR 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => by
    obtain ⟨V, hsz, hpo, -⟩ := onVR h
    have bd := VG.Proof.Dsa.supported_bounds hsz
    exact WP.of_flat (c := .seq (.block KP0) (.seq Verify.powP (.block ptrY))) (by decide +kernel)
      (stKV0 V fun _ c a7 _ a9 => WP.seq (WP.mono (powV c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega)) a7 (c.xs.sub (by omega)) a9 (by omega) hpo) fun _ c' =>
        WP.mono (ptrY_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ =>
          (fix_CB (c'.keepM k m).cb).app ⟨b7, b8, trivial⟩))

/-- `keyPair`, from `VR`'s phase: `Base` kept. -/
theorem kpV {v : VD} {s : State} (h : ΦVR v s) : WP isa Sign.keyPair s (Base v) := by
  obtain ⟨V, hsz, hpo, -⟩ := onVR h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have B := V.cb.1
  have hL := B.ok
  refine WP.mono (keyPair_ok hL B.scr B.regs V.cb.2.1 V.cb.2.2.1 V.xs V.cb.2.2.2.1 (by omega) hpo V.cb.2.2.2.2)
    fun t ⟨⟨_, _, _, m, o, w⟩, k⟩ => ?_
  have K : BKept v.L s.mem t.mem := (BKept.ofBody hL (PLow.body hL o)).trans (BKept.ofMask hL w)
  exact B.step (B.regs.ofBKept k K) k.2.1 k.2.2 K.out (K.word (by decide) (by decide)) (K.word (by decide) (by decide))

theorem pinsV64 : Pins (At ΦVR FVR 64) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := Sign.keyPair) (by decide +kernel) ((kpV h).mono fun _ B => B.fixB)

theorem pinsV65 : Pins (At ΦVR FVR 65) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envQ v) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.block enterQ)) (by decide +kernel)
      (WP.seq ((kpV h).mono fun _ B => WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ =>
        (B.keepM k m).fixB.app (fix_envQ iq)))

theorem pinsV69 : Pins (At ΦVR FVR 69) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.seq (.block enterQ) (.seq (zeroArr 7) (.block Sign.ptrX))))
      (by decide +kernel)
      (WP.seq ((kpV h).mono fun _ B => WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => by
        have B1 := B.keepM k m
        have hL := B.ok
        have hwq := hL.wq_ge
        have hqs := hL.qslot
        have e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
        have e7 := e 7; have e8 := e 8; have e28 := e 28
        refine WP.seq (WP.mono (zeroArr_ok iq.env (j := 7) (by decide)) fun _ ⟨⟨_, o⟩, k'⟩ => ?_)
        have B2 := B1.body k' (Body.ofQ hL o (by omega))
        have iq2 := iq.keep k'
        exact WP.mono (ptrX_ok B2.scr hL B2.regs) fun _ ⟨⟨c7, c8, m'⟩, k''⟩ =>
          ((B2.keepM k'' m').fixB.app (fix_envQ (iq2.keep k''))).app ⟨c7, c8, trivial⟩)))

theorem VR_rel : RelCT isa (Two ΦVR) VR fun _ _ => True := by
  refine chain_start (chain_cons runVR (m := 2) (by decide) (two_taint _ pinsV0 (by taint_decide)) ?_)
  refine chain_cons runVR (m := 12) (by decide) (two_taint _ pinsV2 (by taint_decide)) ?_
  refine chain_cons runVR (m := 53) (by decide) (two_taint _ pinsV12 (by taint_decide)) ?_
  refine chain_cons runVR (m := 64) (by decide) (two_taint _ pinsV53 (by taint_decide)) ?_
  refine chain_cons runVR (m := 65) (by decide) (two_taint _ pinsV64 (by taint_decide)) ?_
  refine chain_cons runVR (m := 69) (by decide) (two_taint _ pinsV65 (by taint_decide)) ?_
  exact two_taint _ pinsV69 (by taint_decide)

/-! ## The levels' relations -/

theorem Kv_rel : RelCT isa (Two ΦKv) RKv fun _ _ => True := by
  refine chain_start (chain_cons runKv (m := 1) (by decide)
    (two_taint _ (pinsL rfl (pinsK_0 onKv)) (by taint_decide)) ?_)
  refine chain_cons runKv (m := 28) (by decide) (two_taint _ (pinsL rfl (pinsK_1 onKv)) (by taint_decide)) ?_
  exact chain_cons runKv (m := 29) (by decide) (rel_ite_at hFKv zeroKv VR_rel fail_rel) nil_rel

theorem R3v_rel : RelCT isa (Two ΦR3v) R3v fun _ _ => True := by
  refine chain_start (chain_cons runR3v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3v)) (by taint_decide)) ?_)
  refine chain_cons runR3v (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3v)) (by taint_decide)) ?_
  refine chain_cons runR3v (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3v)) (by taint_decide)) ?_
  refine chain_cons runR3v (m := 46) (by decide) (rel_ite_at hFR3gv (zeroL rfl (zeroEg onR3v))
    (eo_rel runEgv fun _ _ h => semEg onR3v ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3v (m := 47) (by decide) (rel_ite_at hFR3v (zeroL rfl (zeroR3 onR3v)) Kv_rel fail_rel)
    nil_rel

theorem R2v_rel : RelCT isa (Two ΦR2v) R2v fun _ _ => True := by
  refine chain_start (chain_cons runR2v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2v)) (by taint_decide)) ?_)
  refine chain_cons runR2v (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2v)) (by taint_decide)) ?_
  refine chain_cons runR2v (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2v)) (by taint_decide)) ?_
  exact chain_cons runR2v (m := 24) (by decide) (rel_ite_at hFR2v (zeroL rfl (zeroR2 onR2v)) R3v_rel fail_rel)
    nil_rel

theorem R1v_rel : RelCT isa (Two ΦR1v) R1v fun _ _ => True :=
  chain_start (chain_cons runR1v (m := 1) (by decide) (relL rfl rfl (relR1 onR1v))
    (chain_cons runR1v (m := 2) (by decide) (rel_ite_at hFR1v (zeroL rfl (zeroR1 onR1v)) R2v_rel fail_rel)
      nil_rel))

theorem R0v_rel : RelCT isa (Two ΦR0v) R0v fun _ _ => True :=
  chain_start (chain_cons runR0v (m := 1) (by decide) (relL rfl rfl (relR0 onR0v))
    (chain_cons runR0v (m := 2) (by decide) (rel_ite_at hFR0v (zeroL rfl (zeroR0 onR0v)) R1v_rel fail_rel)
      nil_rel))

theorem X2v_rel : RelCT isa (Two ΦX2v) X2v fun _ _ => True :=
  chain_start (chain_cons runX2v (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2v)) (by taint_decide))
    (chain_cons runX2v (m := 13) (by decide) (rel_ite_at hFX2v (zeroL rfl (zeroX2 onX2v)) R0v_rel fail_rel)
      nil_rel))

theorem X1v_rel : RelCT isa (Two ΦX1v) X1v fun _ _ => True := by
  refine chain_start (chain_cons runX1v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1v)) (by taint_decide)) ?_)
  refine chain_cons runX1v (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1v)) (by taint_decide)) ?_
  refine chain_cons runX1v (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1v)) (by taint_decide)) ?_
  exact chain_cons runX1v (m := 6) (by decide) (rel_ite_at hFX1v (zeroL rfl (zeroX1 onX1v)) X2v_rel fail_rel)
    nil_rel

theorem s6_keptv : ∀ i ∈ instrs (seg FTv 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTv 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTv6 : Pins (At C0v FTv 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTv (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0v) (F := FTv) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Params.entry) rfl (frontV _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptv e₂ rfl).trans h₁, trivial⟩

theorem pins_a4v {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → vdV s = v) : Pins Φ [.a4] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact congrArg (fun v : VD => v.L.S) ((h _ _ h₁).trans (h _ _ h₂).symm)

theorem validatePriv_rel : RelCT isa (Two C0v) PrevalidatedSign.validate fun _ _ => True := by
  refine chain_start (chain_cons runTv (m := 1) (by decide)
    (two_taint _ (pins_mono (pins_a4v fun _ _ h => h.2) fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTv (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 6) (by decide) (rel_ite_at hFTv (zeroL rfl (zeroT frontV)) X1v_rel fail_rel) ?_
  exact two_taint _ pinsTv6 (by taint_decide)

/-- Runs that agree on the contract's public data have the same public data `vdV`. -/
theorem vdV_eq {s t : State} (hs : vpkContract.pre s) (hp : vpkContract.pub s t) : vdV s = vdV t := by
  obtain ⟨-, e0, e1, e2, e3, e4, e5, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.1
  obtain ⟨hl, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at hl
  have e := (List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp hl
  rw [← e0, ← e1, ← e2, ← e3, Nat.min_eq_right (by omega)] at e
  simp only [vdV, playOf]
  rw [e, e0, e2, e3, e4, e5]

theorem validatePriv_ct : ConstantTime isa vpkContract.pre vpkContract.pub PrevalidatedSign.validate :=
  RelCT.constantTime (validatePriv_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdV s, ⟨hs, rfl⟩, ⟨ht, (vdV_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
