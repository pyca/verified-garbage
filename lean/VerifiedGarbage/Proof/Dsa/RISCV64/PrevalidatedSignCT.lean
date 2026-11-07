module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

-- separate module: the taint checks of its levels cost more than their imports, and the registration
-- states the result without them

/-!
# DSA prevalidated signing on RISC-V: constant time

`vg_dsa_sign_prevalidated` (`PrevalidatedSign.sign`) runs `vg_dsa_sign`'s
entry and, as `vg_dsa_verify_prevalidated` does (`PrevalidatedCT.lean`), of
the checks of the key only the sizes, then sets up the working spaces
(`setupQ`, `setupP`) and runs `PrevalidatedSign.body`. Its levels up to the
sizes' branch are signing's (`SignCT.lean`), failing to `zeroOut`. The sizes'
passing side `XRsp` is cut at 0, 2 (after `enterQ; ptrQ`), 11 (after
`enterP; ptrP`) and 26 (before `setMask`); from 27 on it is signing's tail
(`tail_rel`), whose phase `TS` holds since the precondition makes the
domain valid (`km_of`) and `setMask` leaves a mask in `hMask`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv at_step take_split)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-! ## The levels -/

/-- On entry. -/
def C0sp (v : VD) (s : State) : Prop := spContract.pre s ∧ vdS s = v

theorem C0sp.c0s {v : VD} {s : State} (h : C0sp v s) : C0s v s := ⟨h.1.1, h.2⟩

theorem frontSp : ∀ v s, C0sp v s → WP isa (.block Sign.entry) s (P0 v) := fun v s h => frontS v s h.c0s

/-- After the sizes. -/
abbrev XRsp : Prog isa := .seq setupQ (.seq setupP PrevalidatedSign.body)
abbrev X2sp : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs XRsp Sign.zeroOut)
abbrev X1sp : Prog isa :=
  .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2sp Sign.zeroOut)

abbrev FTsp : List (Prog isa) := Code.flat PrevalidatedSign.sign
abbrev FX1sp : List (Prog isa) := Code.flat X1sp
abbrev FX2sp : List (Prog isa) := Code.flat X2sp
abbrev FRsp : List (Prog isa) := Code.flat XRsp

abbrev ΦX1sp (v : VD) (u : State) : Prop := At C0sp FTsp 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2sp (v : VD) (u : State) : Prop := At ΦX1sp FX1sp 5 v u ∧ u.gpr .a0 = 0
abbrev ΦRsp (v : VD) (u : State) : Prop := At ΦX2sp FX2sp 12 v u ∧ u.gpr .a0 = 0

theorem hFTsp : (FTsp.drop 5).take 1 = [.ite (.zero .a0) X1sp Sign.zeroOut] := rfl
theorem hFX1sp : (FX1sp.drop 5).take 1 = [.ite (.zero .a0) X2sp Sign.zeroOut] := rfl
theorem hFX2sp : (FX2sp.drop 12).take 1 = [.ite (.zero .a0) XRsp Sign.zeroOut] := rfl

theorem runTsp : ∀ v s, C0sp v s → WP isa (Code.seqL FTsp) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := signPre_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1sp : ∀ v s, ΦX1sp v s → WP isa (Code.seqL FX1sp) s fun _ => True := run_then runTsp hFTsp
theorem runX2sp : ∀ v s, ΦX2sp v s → WP isa (Code.seqL FX2sp) s fun _ => True := run_then runX1sp hFX1sp
theorem runRsp : ∀ v s, ΦRsp v s → WP isa (Code.seqL FRsp) s fun _ => True := run_then runX2sp hFX2sp

theorem onX1sp : ∀ v u, ΦX1sp v u → SX1 v u := fun _ _ h => semX1 frontSp ⟨atL rfl h.1, h.2⟩
theorem onX2sp : ∀ v u, ΦX2sp v u → SX2 v u := fun _ _ h => semX2 onX1sp ⟨atL rfl h.1, h.2⟩
theorem onRsp : ∀ v u, ΦRsp v u → P1 v u := fun _ _ h => semR0 onX2sp ⟨atL rfl h.1, h.2⟩

theorem outSp : ∀ v s, C0sp v s → v.out = some (oOf v) := fun v s h => outS v s h.c0s
theorem oX1sp : ∀ v u, ΦX1sp v u → v.out = some (oOf v) := fun _ _ h => at_pure outSp h.1
theorem oX2sp : ∀ v u, ΦX2sp v u → v.out = some (oOf v) := fun _ _ h => at_pure oX1sp h.1

/-! ## The domain is valid -/

theorem vdS_bytes (s : State) {o k : Nat} (hk : o + k ≤ 3 * (s.gpr .a4).toNat + (s.gpr .a6).toNat) :
    Spec.Rsa.bytesAt s.mem (off (s.gpr .a2) o) k = (vdS s).sl o k := by
  rw [VD.sl, ← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a2) hk]; rfl

/-- The domain passes its checks, on the public data. -/
theorem km_of {v : VD} {s : State} (h : C0sp v s) : KM v := by
  obtain ⟨hp, rfl⟩ := h
  obtain ⟨hsh, hpub, -⟩ := spre_valid hp
  have hv := hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have b0 := vdS_bytes s (o := 0) (k := (s.gpr .a4).toNat) (by omega)
  rw [off, BitVec.add_zero] at b0
  have ep : pOf s.mem (slayOf s) (s.gpr .a2) = (vdS s).p := by rw [pOf]; exact congrArg _ b0
  have eq : qOf s.mem (slayOf s) (s.gpr .a2) = (vdS s).q := by
    rw [qOf]; exact congrArg _ (vdS_bytes s (by simp only [slayOf]; omega))
  rw [ep, eq] at hsh hpub
  have bd := VG.Proof.Dsa.supported_bounds hsh.1
  exact ⟨hsh.1, hsh.2.2, hsh.2.1, (pmod_iff (by omega) (by omega)).mp hpub.2.1⟩

theorem kmX1 {v : VD} {u : State} (h : ΦX1sp v u) : KM v := at_pure (G := KM) (fun _ _ h => km_of h) h.1
theorem kmX2 {v : VD} {u : State} (h : ΦX2sp v u) : KM v := at_pure (G := KM) (fun _ _ h => kmX1 h) h.1
theorem kmR {v : VD} {u : State} (h : ΦRsp v u) : KM v := at_pure (G := KM) (fun _ _ h => kmX2 h) h.1

theorem gsR {v : VD} {u : State} (h : ΦRsp v u) : GS v :=
  at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => at_pure (G := GS) (fun _ _ h => gC0s _ _ h.c0s)
    h.1) h.1) h.1

theorem osR {v : VD} {u : State} (h : ΦRsp v u) : OS v u :=
  os_at (fun _ _ h => os_at (fun _ _ h => os_at (fun _ _ h => osC0s _ _ h.c0s) h.1) h.1) h.1

/-- What the tail needs of the public data, from the domain's checks. -/
theorem tv_of {v : VD} {s : State} (B : Base v s) (hk : KM v) : TV v := by
  obtain ⟨hsz, hp, hq, -⟩ := hk
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have hl := B.q_lt
  refine ⟨hsz, ⟨by omega, hq, hl, q_bits (by omega) hl, by omega, hp⟩, fun m => ?_⟩
  have hq8 : Spec.Dsa.bitLength v.q = 8 * (Spec.Dsa.bitLength v.q / 8) := by
    have : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength v.p) (Spec.Dsa.bitLength v.q) := hsz
    unfold Spec.Dsa.supportedSizes at this; omega
  refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
  rw [VG.Proof.Bignum.bytesAt_length]
  refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)) ?_
  have := pow_bitLength_le (q := v.q) (by omega)
  rw [hq8, Nat.pow_mul] at this
  exact this

/-! ## `XRsp` -/

theorem pinsRsp_0 : Pins (At ΦRsp FRsp 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (onRsp _ _ h).1.fixB⟩

theorem pinsRsp_2 : Pins (At ΦRsp FRsp 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key v.L.pl), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h => by
    have B := (onRsp _ _ h).1
    refine WP.of_flat (c := .seq (.block enterQ) (.block ptrQ)) rfl
      (WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => ?_))
    have B1 := B.keepM k m
    exact WP.mono (ptrQ_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
      ((B1.keepM k' m').fixB.app (fix_envQ (iq.keep k'))).app ⟨a7, a8, trivial⟩

theorem pinsRsp_11 : Pins (At ΦRsp FRsp 11) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq setupQ (.seq (.block enterP) (.block ptrP))) rfl
      (WP.seq (WP.mono (setupQ_P1 (onRsp _ _ h) (kmR h)) fun _ hs => by
        have B := hs.1.1.1
        refine WP.seq (WP.mono (enterP_ok B.ok B.scr B.regs) fun _ ⟨⟨ip, m⟩, k⟩ => ?_)
        have B1 := B.keepM k m
        exact WP.mono (ptrP_ok B1.scr B1.ok B1.regs) fun _ ⟨⟨a7, a8, m'⟩, k'⟩ =>
          ((B1.keepM k' m').fixB.app (fix_envP (ip.keep k'))).app ⟨a7, a8, trivial⟩))

/-- The working spaces set up. -/
theorem setup_CK {v : VD} {s : State} (h : ΦRsp v s) : WP isa (.seq setupQ setupP) s (CK v) :=
  WP.seq (WP.mono (setupQ_P1 (onRsp _ _ h) (kmR h)) fun _ hs => (setupP_SR3 hs).mono fun _ ⟨c, _⟩ => c)

theorem pinsRsp_26 : Pins (At ΦRsp FRsp 26) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq setupQ setupP) (by decide +kernel) ((setup_CK h).mono fun _ c => fix_CK c)

/-- `setMask` after the setup: the tail's phase. -/
theorem setMask_TS {v : VD} {s : State} (h : ΦRsp v s) :
    WP isa (.seq setupQ (.seq setupP (.block PrevalidatedSign.setMask))) s (TS v) := by
  have os₀ := osR h
  refine WP.seq (WP.mono (WP.rdwr (setupQ_P1 (onRsp _ _ h) (kmR h))) fun s₁ ⟨hs, r₁, w₁, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (setupP_SR3 hs)) fun t ⟨⟨c, _⟩, r₂, w₂, _⟩ => ?_)
  have hL := c.base.ok
  have hZ := hL.z256
  have P : PK v t := ⟨⟨c.base, c.inp, c.inv, c.p0, c.p24⟩, c.lens, c.q0, os₀.keep (r₂.trans r₁) (w₂.trans w₁)⟩
  obtain ⟨_, hal0⟩ := ScrL.hdr c.base.scr hL (d := 0) (by decide) (by decide)
  have hst : InRegions t.wr (off v.L.S 0) 8 := c.base.scr.st (by omega)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.mem = t.mem.writeW (off v.L.S 0) (mask true))
    (by brun [PrevalidatedSign.setMask, exec_li (show imm12 (-1) by decide), hMask, c.base.regs.s6, hst, hal0]; rfl)
    (by decide) (by rfl)) fun u ⟨mu, ku⟩ => ?_
  have wo : Outside v.L.S hMask 8 t.mem u.mem := by
    rw [mu]; exact writeW_outside t.mem v.L.S _ (by simp only [hMask]; omega)
  refine ⟨⟨P.frame ku ⟨c.inp.env.keep ku, (ku.gpr (by decide)).trans c.inp.s6⟩ ?_ (BKept.ofMask hL wo)
      (mask_arrP hL wo 0 (by decide)) (mask_arrP hL wo 24 (by decide)) (keepQ_arr0 hL (mask_keepQ hL wo)),
    ⟨true, by rw [mu]; exact word_writeW_self t.mem v.L.S hMask _⟩⟩, gsR h, tv_of c.base (kmR h)⟩
  show ((word u.mem v.L.S (slot v.L.wp 0)).toNat * (u.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [mask_word0 hL wo, ku.gpr (by decide)]
  exact c.inv

theorem drop27 : FRsp.drop 27 = FTl := by decide +kernel

theorem XRsp_rel : RelCT isa (Two ΦRsp) XRsp fun _ _ => True := by
  refine chain_start (chain_cons runRsp (m := 2) (by decide) (two_taint _ pinsRsp_0 (by taint_decide)) ?_)
  refine chain_cons runRsp (m := 11) (by decide) (two_taint _ pinsRsp_2 (by taint_decide)) ?_
  refine chain_cons runRsp (m := 26) (by decide) (two_taint _ pinsRsp_11 (by taint_decide)) ?_
  refine chain_cons runRsp (m := 27) (by decide) (two_taint _ pinsRsp_26 (by taint_decide)) ?_
  rw [drop27]
  exact relCT_flat (tail_rel (run_drop runRsp drop27) fun _ _ h =>
    at_sem (Φ := ΦRsp) (F := FRsp) (n := 27) (M := TS)
      (fun _ _ h' => WP.of_flat (c := .seq setupQ (.seq setupP (.block PrevalidatedSign.setMask)))
        (by decide +kernel) (setMask_TS h')) h)

/-! ## The sizes' levels -/

theorem X2sp_rel : RelCT isa (Two ΦX2sp) X2sp fun _ _ => True :=
  chain_start (chain_cons runX2sp (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2sp)) (by taint_decide))
    (chain_cons runX2sp (m := 13) (by decide) (rel_ite_at hFX2sp (zeroL rfl (zeroX2 onX2sp)) XRsp_rel
      (szero_rel (run_else runX2sp hFX2sp)
        (fun _ _ h => (at_sem (Φ := ΦX2sp) (F := FX2) (n := 12) (M := MX2) (fun _ _ h => midX2 onX2sp h)
          (atL rfl h.1)).1) fun _ _ h => at_pure oX2sp h.1)) nil_rel))

theorem X1sp_rel : RelCT isa (Two ΦX1sp) X1sp fun _ _ => True := by
  refine chain_start (chain_cons runX1sp (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1sp)) (by taint_decide)) ?_)
  refine chain_cons runX1sp (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1sp)) (by taint_decide)) ?_
  refine chain_cons runX1sp (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1sp)) (by taint_decide)) ?_
  exact chain_cons runX1sp (m := 6) (by decide) (rel_ite_at hFX1sp (zeroL rfl (zeroX1 onX1sp)) X2sp_rel
    (szero_rel (run_else runX1sp hFX1sp)
      (fun _ _ h => (at_sem (Φ := ΦX1sp) (F := FX1) (n := 5) (M := MX1) (fun _ _ h => midX1 onX1sp h)
        (atL rfl h.1)).1.1) fun _ _ h => at_pure oX1sp h.1)) nil_rel

theorem s6_keptsp : ∀ i ∈ instrs (seg FTsp 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTsp 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTsp6 : Pins (At C0sp FTsp 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTsp (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0sp) (F := FTsp) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Sign.entry) rfl (frontSp _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptsp e₂ rfl).trans h₁, trivial⟩

theorem signPre_rel : RelCT isa (Two C0sp) PrevalidatedSign.sign fun _ _ => True := by
  refine chain_start (chain_cons runTsp (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0s)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (sentry_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, (at_zero_inv h₁).c0s, (at_zero_inv h₂).c0s, hsp⟩) fun _ _ h => h
  refine chain_cons runTsp (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontSp)) (by taint_decide)) ?_
  refine chain_cons runTsp (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontSp)) (by taint_decide)) ?_
  refine chain_cons runTsp (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontSp)) (by taint_decide)) ?_
  refine chain_cons runTsp (m := 6) (by decide) (rel_ite_at hFTsp (zeroL rfl (zeroT frontSp)) X1sp_rel
    (szero_rel (run_else runTsp hFTsp) (fun _ _ h => (at_sem (Φ := C0sp) (F := TF Sign.entry) (n := 5) (M := MT)
        (fun _ _ h => midT frontSp h) (atL rfl h.1)).1.1)
      fun _ _ h => at_pure outSp h.1)) ?_
  exact two_taint _ pinsTsp6 (by taint_decide)

theorem signPre_ct : ConstantTime isa spContract.pre spContract.pub PrevalidatedSign.sign :=
  RelCT.constantTime (signPre_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdS s, ⟨hs, rfl⟩, ⟨ht, (vdS_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
