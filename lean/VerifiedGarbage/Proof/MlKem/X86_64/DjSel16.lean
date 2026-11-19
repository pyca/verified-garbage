module

public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
public import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
meta import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
public import VerifiedGarbage.Proof.MlKem.X86_64.Lay
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lay
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public meta import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public meta import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
public meta import Lean.Elab.Tactic.ElabTerm
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncBase

/-! ### `MlKem.X86_64.Top16Ctl`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: the control flow and the stack pointer of the top-level functions with 16-bit polynomials

As `s4_ctl` and `s4_sp` (`Sample4Impl.lean`), for code that also calls the
16-bit sampler `c` of an implementation `v` (`S : S16Ok c`) and the K-PKE
functions (`hK : KpkeOk L`): their calls are taken from `S` and `hK`, before
any part is evaluated, so the kernel evaluates neither the samplers' code
nor the K-PKE functions'.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v` or `c`, or a part of the
top-level functions that calls the K-PKE functions: the kernel evaluates
only the parts that call neither the samplers nor the K-PKE functions. -/
elab "closed16_in " v:ident c:ident : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  for x in [v, c] do
    let e ← elabTerm x none
    if g.containsFVar e.fvarId! then throwError "the goal mentions {e}"
  let calls := [``Impl.MlKem.X86_64.kemKeyGen16, ``Impl.MlKem.X86_64.kemEncapsH16,
    ``Impl.MlKem.X86_64.Top16.kgTail, ``Impl.MlKem.X86_64.Top16.kgRest,
    ``Impl.MlKem.X86_64.Top16.encRest, ``Impl.MlKem.X86_64.Top16.encrypt,
    ``Impl.MlKem.X86_64.Kem.kpkeKgAt, ``Impl.MlKem.X86_64.Kem.kpkeEncAt, ``Impl.MlKem.X86_64.Kem.kpkeDecAt,
    ``Impl.MlKem.X86_64.kpkeKg, ``Impl.MlKem.X86_64.kpkeEnc, ``Impl.MlKem.X86_64.kpkeDec]
  if (g.find? fun e => e.isConst && calls.contains e.constName!).isSome then
    throwError "the goal calls the K-PKE functions"

open Lean Meta Elab Tactic in
/-- Puts the code `X` of a goal `f X = true` in weak head normal form, if
that is a `block`, `seq`, `ite` or `call`, so that a lemma about each applies with
reducible transparency: a failed `apply` at default transparency would
evaluate `f` on code it does not match, the K-PKE functions' included. -/
elab "code_whnf" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, rhs) := t.eq? | throwError "not an equation"
  let lhs := lhs.consumeMData
  let .app f x := lhs | throwError "not an application"
  let x' ← whnf x
  unless [``Code.block, ``Code.seq, ``Code.ite, ``Code.call].contains x'.getAppFn.constName do
    throwError "not a `block`, `seq`, `ite` or `call`"
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq (.app f x') rhs)]

/-- `ctlOk` of a top-level function with 16-bit polynomials. -/
tactic_template "s16_ctl " v:ident c:ident S:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($hK).kg.ctl | with_reducible exact ($hK).enc.ctl
    | with_reducible exact ($hK).dec.ctl | with_reducible exact ($S).mxcsr
    | (closed16_in $v $c; decide +kernel) | (code_whnf; closed16_in $v $c; decide +kernel)
    | with_reducible exact ($v).prfs_ctl _ _ _ _ | with_reducible exact ($v).arith.cbd16.ctl
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite)
    | (code_whnf; with_reducible apply ctlOk_call)))

section
open VG.X86_64

/-- Whether the calls and frames of `c` use at most `k` bytes of stack, for
`s16_xd`. -/
def xdLe (k : Nat) (c : Prog isa) : Bool := Nat.ble c.x86_64Depth k

theorem xdLe_spec {k : Nat} {c : Prog isa} (h : xdLe k c = true) : c.x86_64Depth ≤ k :=
  Nat.le_of_ble_eq_true h

theorem xdLe_of_le {k : Nat} {c : Prog isa} (h : c.x86_64Depth ≤ k) : xdLe k c = true :=
  Nat.ble_eq_true_of_le h

theorem xdLe_seq {k : Nat} {a b : Prog isa} (ha : xdLe k a = true) (hb : xdLe k b = true) :
    xdLe k (.seq a b) = true :=
  xdLe_of_le (xd_seq (xdLe_spec ha) (xdLe_spec hb))

theorem xdLe_ite {k : Nat} {f : Cond} {a b : Prog isa} (ha : xdLe k a = true) (hb : xdLe k b = true) :
    xdLe k (.ite f a b) = true :=
  xdLe_of_le (Nat.max_le.2 ⟨xdLe_spec ha, xdLe_spec hb⟩)

theorem xdLe_call {k : Nat} {n : String} {b : Prog isa} (h : xdLe k b = true) : xdLe (k + 8) (.call n b) = true :=
  xdLe_of_le (Nat.add_le_add_right (xdLe_spec h) 8)

theorem xdLe_callee {k : Nat} {kk : Contract isa} {c : Prog isa} (h : CalleeOk kk c) : xdLe k c = true :=
  xdLe_of_le (by rw [x86_64Depth_zero h.nosp h.depth]; exact Nat.zero_le _)

theorem xdLe_s16 {k : Nat} {c : Prog isa} (S : S16Ok c) (hk : 24 ≤ k) : xdLe k c = true :=
  xdLe_of_le (by rw [x86_64Depth_noSp S.nosp]; have := S.depth_le; omega_using [hk, this])

theorem xdLe_prfs {k : Nat} (v : Sample4Impl) (N₀ n o wl : Nat) (hk : 16 ≤ k) :
    xdLe k (v.callee.prfs N₀ n o wl) = true :=
  xdLe_of_le (Nat.le_trans (v.prfs_xd N₀ n o wl) hk)

/-- That the calls of a top-level function with 16-bit polynomials use at
most `k` bytes of stack (a goal `xdLe k _ = true`): closed code by evaluation first, then code
that is a `seq`, `ite` or `call` as it stands, then the callees' lemmas, by `apply` (an `exact`
that does not apply looks for a coercion before it fails, at every node of the code). -/
tactic_template "s16_xd " v:ident c:ident S:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | (closed16_in $v $c; decide +kernel)
    | with_reducible exact xdLe_block _
    | with_reducible apply xdLe_seq | with_reducible apply xdLe_ite | with_reducible apply xdLe_call
    | with_reducible apply xdLe_callee ($hK).kg | with_reducible apply xdLe_callee ($hK).enc
    | with_reducible apply xdLe_callee ($hK).dec | with_reducible apply xdLe_s16 $S (by decide)
    | (code_whnf; closed16_in $v $c; decide +kernel)
    | with_reducible apply xdLe_prfs $v _ _ _ _ (by decide) | with_reducible apply xdLe_callee ($v).arith.cbd16
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite)
    | (code_whnf; with_reducible apply xdLe_call)))

end

/-- That a top-level function with 16-bit polynomials never writes the stack pointer. -/
tactic_template "s16_sp " v:ident c:ident S:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($hK).kg.sp | with_reducible exact ($hK).enc.sp
    | with_reducible exact ($hK).dec.sp | with_reducible exact ($S).spSafe
    | (closed16_in $v $c; exact Code.all_of_spTest (by decide +kernel))
    | (code_whnf; closed16_in $v $c; exact Code.all_of_spTest (by decide +kernel))
    | with_reducible exact ($v).prfs_sp _ _ _ _ | with_reducible exact ($v).arith.cbd16.sp
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite)
    | (code_whnf; with_reducible apply all_call)))

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.Sel16`, which the modules that import this one used -/

section

/-! ### `MlKem.X86_64.EcTop16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: encapsulation with `H(ek)` given, with 16-bit polynomials

As with polynomials of `u32`s (`EcTop.lean`), but for K-PKE.Encrypt with
16-bit polynomials (`Enc16.lean`), which writes the ciphertext straight to
`ct`, so that the outputs are only `K` copied to `key`
(`kemEncapsH16_correct`, `kemEncapsH16_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Encaps16

open Encaps VG.Impl.MlKem.X86_64.EncapsH

variable (K : Kem16)

/-- What encapsulation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Ec16Wf : Prop extends EcWfB K.L where
  enc : Enc16.EncChks K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0)
  tl : Enc16.tailChk K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0) (.r13, 0) = true
  o₁T : keepB (ecB K.L) [((.r12, 0), 32)] (.r13, 0) K.L.ctLen = true

variable {K}

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO16 (W : Ec16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (ecC W.toEcWfB σ) (.r13, 0) (ecEk K.L σ) (ecMs σ) (ecG K.L σ).2 s

theorem out_ok (W : Ec16Wf K) {σ : State} {s : State} (h : EncO16 W σ s) :
    WP isa (copy (.r12, 0) (sc oG) 32) s (ECEnd K.L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay W.toEcWfB hp
  refine WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  refine ⟨h.out.2.ec.step W.toEcWfB hp hP₁.b W.o₁K, by rw [hP₁.cs .r15 (by decide)]; exact h.r15, ?_, fun ho => ?_⟩
  · rw [hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [L₀.keepBytes hP₁.b W.o₁T]; exact h.ct ho

end Encaps16

open Encaps Encaps16 in
theorem kemEncapsH16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) (hctl : ctlOk (kemEncapsH16 K v.callee (n, c)) = true)
    (σ : State) (hp : (encapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemEncapsH16 K v.callee (n, c)) σ t s' ∧ abiPreserved σ s' ∧ (encapsK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (hCopy_ok W.toEcWfB hp h₁) fun s₂ ⟨h₂, hH, h15⟩ =>
      WP.seq (WP.mono (hashes_ok W.toEcWfB hp h₂ hH h15) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc16.encrypt_ok hK v hs (C := ecC W.toEcWfB σ) (show Reg.r14 ∉ argRegs by decide)
            (by decide) W.k.2 W.enc W.tl h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok W h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin W.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encapsK K.L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

namespace Encaps16

open Encaps VG.Impl.MlKem.X86_64.EncapsH

variable {K : Kem16}

theorem encrypt_tr (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String} {c : Prog isa}
    (hs : v.callee.s16 = some (n, c)) :
    RelCT isa (R K.L (EncI W.toEcWfB)) (Top16.encrypt K v.callee (n, c) (.r14, 0) (.r13, 0)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧
      Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) ρ x ∧ Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc16.encrypt_tr hK v hs (C := ecCA W.toEcWfB) (show Reg.r14 ∉ argRegs by decide)
        (by decide) W.k.2 W.enc W.tl W.ijT rhoT (ρ := ρ)) (fun _ _ h => h) fun _ _ _ => trivial) ?_
    fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) (Enc.rhoE K.L (ecEk K.L σ₁)) x :=
    ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) (Enc.rhoE K.L (ecEk K.L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE K.L (ecEk K.L σ₁), ec_lrel W.toEcWfB p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr (W : Ec16Wf K) : RelCT isa (R K.L (EncO16 W)) (copy (.r12, 0) (sc oG) 32) fun _ _ => True := by
  obtain ⟨_, oT₁⟩ := W.oT₁
  exact rel2_of (trL W.toEcWfB oT₁) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ec_lrel W.toEcWfB p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec

end Encaps16

open Encaps Encaps16 in
theorem kemEncapsH16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) :
    ConstantTime isa (encapsK K.L).pre (encapsK K.L).pub (kemEncapsH16 K v.callee (n, c)) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncapsH16
  refine RelCT.seq (relInv (I' := ProOut K.L) (fun σ s hp hs => by subst hs; exact pro_ok W.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => EC K.L σ s ∧ bytesAt s.mem (pa s (sc oH)) 32 = H (ecEk K.L σ) ∧
    s.gpr .r15 = 1) (fun σ s hp hs => hCopy_ok W.toEcWfB hp hs) hCopy_tr) ?_
  refine RelCT.seq (relInv (I' := EncI W.toEcWfB) (fun σ s hp hs => hashes_ok W.toEcWfB hp hs.1 hs.2.1 hs.2.2)
    (hashes_tr W.toEcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO16 W) (fun σ s _ hi =>
      Enc16.encrypt_ok hK v hs (C := ecC W.toEcWfB σ) (show Reg.r14 ∉ argRegs by decide) (by decide) W.k.2 W.enc W.tl
        hi.1 hi.2) (encrypt_tr hK v W hs)) ?_
  refine RelCT.seq (relInv (I' := ECEnd K.L) (fun σ s _ hi => out_ok W hi) (out_tr W)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the top-level functions of each implementation

An implementation `v` with a 16-bit sampler (`Callee4.s16`) runs the
top-level functions with 16-bit polynomials (`kemKeyGenSel`, …); the
baseline, those with polynomials of `u32`s. Each is `Verified` by the proof
of the one it runs, against any contract the K-PKE functions' parameter
set's implies. The ones with 16-bit polynomials are proven for the layout
with only the first `n` bytes of `scratch` (`narrowK`), and leave the rest
of it as it was (`keyGenSel_keep`, …).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Key generation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem keyGen16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemKeyGen16 K v.callee (m, c)) = true) (hsat : ∃ s, (keyGenK K.L).pre s) :
    Verified X86_64.target (kemKeyGen16 K v.callee (m, c)) (keyGenK (narrowL K.L n)) :=
  Verified.of_correct (kemKeyGen16_correct (K := narrowK K n) (hK.narrow n) v W16 hs hctl)
    (kemKeyGen16_ct (K := narrowK K n) (hK.narrow n) v W16 hs)
    (.refl (hsat.elim fun _ hs => ⟨_, keyGenK_pre hn hs⟩))

theorem keyGenSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) (W : KeyGen.KgWf K.L) {k : Contract isa}
    (hk : (keyGenK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemKeyGen16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemKeyGen K.L v.callee) = true) :
    Verified X86_64.target (kemKeyGenSel K v.callee) k := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (m, c) =>
    exact Verified.of_implies (keyGenK_widen hn
      (keyGen16_narrow hn hK v W16 hs (hctl16 m c (v.s16 m c hs)) hk.sat_left) hk.sat_left) hk
  | none => exact Verified.of_correct (kemKeyGen_correct v W hctl) (kemKeyGen_ct v W) hk

/-- Key generation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem keyGenSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemKeyGen16 K v.callee (m, c)) = true) (hsp : SpSafe (kemKeyGen16 K v.callee (m, c)))
    (hd : (kemKeyGen16 K v.callee (m, c)).x86_64Depth ≤ 32) {s : State} (hp : (keyGenK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemKeyGenSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .rcx + BitVec.ofNat 64 i) = s.mem (s.gpr .rcx + BitVec.ofNat 64 i) := by
  unfold kemKeyGenSel at he
  rw [hs] at he
  obtain ⟨-, hwr, -, -, -, -, d5, d6, -, -, -, -, -, -, -, b4, -, -, -, o4⟩ := id hp
  refine verified_keepTail (keyGen16_narrow hn hK v W16 hs hctl ⟨s, hp⟩) hsp hd (keyGenK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o4 (fun r hr => ?_) b4 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d5
  · exact .inr d6
  · exact .inl rfl

/-- Encapsulation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem encapsH16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemEncapsH16 K v.callee (m, c)) = true) (hsat : ∃ s, (encapsK K.L).pre s) :
    Verified X86_64.target (kemEncapsH16 K v.callee (m, c)) (encapsK (narrowL K.L n)) :=
  Verified.of_correct (kemEncapsH16_correct (K := narrowK K n) (hK.narrow n) v W16 hs hctl)
    (kemEncapsH16_ct (K := narrowK K n) (hK.narrow n) v W16 hs)
    (.refl (hsat.elim fun _ hs => ⟨_, encapsK_pre hn hs⟩))

theorem encapsHSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) (W : Encaps.EcWf K.L) {wc wd : List Nat} (C : KemCalls K.L wc wd)
    {k : Contract isa} (hk : (encapsK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemEncapsH16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemEncapsH K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsHSel K v.callee) k := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (m, c) =>
    exact Verified.of_implies (encapsK_widen hn
      (encapsH16_narrow hn hK v W16 hs (hctl16 m c (v.s16 m c hs)) hk.sat_left) hk.sat_left) hk
  | none => exact Verified.of_correct (kemEncapsH_correct v W C hctl) (kemEncapsH_ct v W C) hk

/-- Encapsulation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem encapsHSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemEncapsH16 K v.callee (m, c)) = true) (hsp : SpSafe (kemEncapsH16 K v.callee (m, c)))
    (hd : (kemEncapsH16 K v.callee (m, c)).x86_64Depth ≤ 32) {s : State} (hp : (encapsK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemEncapsHSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .r9 + BitVec.ofNat 64 i) = s.mem (s.gpr .r9 + BitVec.ofNat 64 i) := by
  unfold kemEncapsHSel at he
  rw [hs] at he
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, d11, d12, -, -, -, -, -, -, -, -, -, -, -, b6, -, -, -, -, -, o6, -⟩ := id hp
  refine verified_keepTail (encapsH16_narrow hn hK v W16 hs hctl ⟨s, hp⟩) hsp hd (encapsK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o6 (fun r hr => ?_) b6 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d11
  · exact .inr d12
  · exact .inl rfl

/-- No instruction of the top-level function `kemKeyGenSel K c` writes the
stack pointer, if neither of the functions it may run does. -/
theorem keyGenSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemKeyGen16 K v.callee (n, c)).all p = true)
    (h : (kemKeyGen K.L v.callee).all p = true) : (kemKeyGenSel K v.callee).all p = true := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

theorem encapsHSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemEncapsH16 K v.callee (n, c)).all p = true)
    (h : (kemEncapsH K.L v.callee).all p = true) : (kemEncapsHSel K v.callee).all p = true := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DcTop`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.Dc16Dec`, which the modules that import this one used -/

section

/-!
# ML-KEM on x86-64: decapsulation with 16-bit polynomials, K-PKE.Decrypt

`m' = K-PKE.Decrypt(dk_PKE, c)` to `M`, in one call of
`vg_mlkem*_kpke_decrypt` (`dec_ok`, `dec_tr`), and what the rest of
decapsulation with 16-bit polynomials needs of the layout (`Dc16Wf`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

variable (K : Kem16)

/-- What `vg_mlkem*_kpke_decrypt` writes. -/
abbrev kdW : List (Ptr × Nat) := [(sc oM, 32), (sc K.oZ, kScr)]

/-- What decapsulation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Dc16Wf : Prop extends DcWfB K.L oCT16 where
  kd : kdChk (dcB K.L) (dcW K.L) K.L (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ) = true
  kdK : dcChk K.L (kdW K) = true
  enc : Enc16.EncChks K (dcB K.L) (dcW K.L) (dckChk K.L) (.rbp, 384 * K.L.k)
  tl : Enc16.tailChk K (dcB K.L) (dcW K.L) (dckChk K.L) (.rbp, 384 * K.L.k) (sc oCT16) = true

variable {K}

/-- `m'` to `M`. -/
theorem dec_ok (hK : KpkeOk K.L) (W : Dc16Wf K) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DC K.L σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) s (DM K.L σ) := by
  have L₀ := h.lay W.toDcWfB hp
  refine WP.mono (kpkeDecAt_okL hK L₀ (by decide) (by decide) rbx_na W.kd) fun s' ⟨hP, hm⟩ =>
    ⟨h.step W.toDcWfB hp hP.b W.kdK, by rw [hP.cs .r15 (by decide)]; exact h15, ?_⟩
  rw [hP.pa rbx_cs, hm, h.c, KPke.decM, KPke.dkPke, ← h.dk]
  exact congrArg (kpkeDecrypt K.L.p · _)
    (bytesAt_take _ _ (show 384 * K.L.p.k ≤ 768 * K.L.p.k + 96 by omega_using [])).symm

theorem dec_tr (hK : KpkeOk K.L) (W : Dc16Wf K) :
    RelCT isa (R K.L fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
      (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) fun _ _ => True :=
  rel2_of (kpkeDecAt_trL hK (by decide) (by decide) rbx_na W.kd) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W.toDcWfB p₁ p₂ pub h₁.1 h₂.1

end Decaps16

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DcSel`, which only this module used -/

section

/-!
# ML-KEM on x86-64: decapsulation, the choice of the key

The comparison of the ciphertexts of `N` bytes (`cmp_ok`: the OR of the XORs
of their words, 0 exactly when they are equal), the mask (`mid_ok`), and the choice of each byte of the key
(`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    WP isa cmpBody s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rdx = s.gpr .rdx ||| (s.mem.readW (s.gpr .rsi) 64 ^^^ s.mem.readW (s.gpr .rdi) 64) ∧
        s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rdi = s.gpr .rdi + 8 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem selBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) (h2 : InRegions s.wr (s.gpr .r8) 1) :
    WP isa selBody s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8) (BitVec.setWidth 8 (((BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) &&& s.gpr .rax) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi)))) ∧
        s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .r8 = s.gpr .r8 + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold selBody
  xrun [h0, h1, h2]

/-- The block between the loops: the mask, and the pointers of the choice. -/
abbrev midB : List Instr := [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
  .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
  .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)]

theorem mask_eq (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by simp; omega_using [h']))
    rw [ifn h, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, decide_eq_false this]
    decide

theorem mid_ok (s : State) :
    WP isa (.block midB) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rax = (if s.gpr .rdx = 0 then BitVec.allOnes 64 else 0) ∧
        s'.gpr .rsi = pa s (sc oG) ∧ s'.gpr .rdi = pa s (sc oKB) ∧ s'.gpr .r8 = pa s (.r12, 0) ∧
        s'.gpr .rcx = BitVec.ofNat 64 32) ∧
      Keep [.rax, .rdx, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oG < 2 ^ 31 by decide), sx_ofNat (show oKB < 2 ^ 31 by decide)]
  exact ⟨mask_eq _, by rw [pa, add_ofNat_zero]⟩

/-! ## The loops -/

theorem sel_byte (x y : Byte) (e : Bool) :
    BitVec.setWidth 8 (((BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) &&& (if e then BitVec.allOnes 64 else 0)) ^^^
      BitVec.setWidth 64 y) = if e then x else y := by
  cases e
  · ext i hi; simp
  · rw [ifp rfl, ifp rfl, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact b8b x

theorem or_xor_eq_zero (d x y : BitVec 64) : d ||| (x ^^^ y) = 0 ↔ d = 0 ∧ x = y := by
  have bit : ∀ i, (d ||| (x ^^^ y)).getLsbD i = (d.getLsbD i || (x.getLsbD i ^^ y.getLsbD i)) := fun i => by
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  constructor
  · intro h
    have hb : ∀ i, d.getLsbD i = false ∧ x.getLsbD i = y.getLsbD i := fun i => by
      have := congrArg (BitVec.getLsbD · i) h
      simp only [bit] at this
      cases hd : d.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
    exact ⟨BitVec.eq_of_getLsbD_eq fun i _ => by rw [(hb i).1]; simp,
      BitVec.eq_of_getLsbD_eq fun i _ => (hb i).2⟩
  · rintro ⟨rfl, rfl⟩
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp

/-- Two words of memory are equal exactly when their eight bytes are. -/
theorem readW64_eq_iff (m : Mem) (a b : Addr) : m.readW a 64 = m.readW b 64 ↔ bytesAt m a 8 = bytesAt m b 8 := by
  constructor
  · intro h
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← byte_readW m a (show 8 * (i + 1) ≤ 64 by omega_using [hi]), h, byte_readW m b (show 8 * (i + 1) ≤ 64 by omega_using [hi])]
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    have e : ∀ c : Addr, (m.readW c 64).getLsbD j = ((m.readW c 64).extractLsb' (8 * (j / 8)) 8).getLsbD (j % 8) := by
      intro c; simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
        Bool.true_and]; congr 1; omega_using []
    have hb := congrArg (fun l => l.getD (j / 8) 0) h
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j / 8 < 8 by omega_using [hj]),
      Option.map_some, Option.getD_some] at hb
    rw [e a, e b, byte_readW m a (show 8 * (j / 8 + 1) ≤ 64 by omega_using [hj]),
      byte_readW m b (show 8 * (j / 8 + 1) ≤ 64 by omega_using [hj]), hb]

theorem bytesAt_eq_succ8 (m : Mem) (a b : Addr) (k : Nat) :
    bytesAt m a (8 * k + 8) = bytesAt m b (8 * k + 8) ↔
      bytesAt m a (8 * k) = bytesAt m b (8 * k) ∧
        m.readW (a + BitVec.ofNat 64 (8 * k)) 64 = m.readW (b + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [bytesAt_add, bytesAt_add, readW64_eq_iff]
  exact ⟨fun h => List.append_inj h (by rw [bytesAt_length, bytesAt_length]), fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩

theorem cmp_ok (s : State) {N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N) (h8 : N % 8 = 0) {a b : Addr}
    (ha : InRegions (s.rd ++ s.wr) a N) (hb : InRegions (s.rd ++ s.wr) b N)
    (hsi : s.gpr .rsi = a) (hdi : s.gpr .rdi = b) (hdx : s.gpr .rdx = 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (N / 8)) :
    WP isa (.loop cmpBody .ne) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (s'.gpr .rdx = 0 ↔ bytesAt s.mem a N = bytesAt s.mem b N) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  have in8 : ∀ {p : Addr}, InRegions (s.rd ++ s.wr) p N → ∀ k < N / 8,
      InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8 := fun h k hk => by
    obtain ⟨r, hr, hc⟩ := h
    exact ⟨r, hr, CallLay.contains_trans hc (by omega_using [hk]) (by omega_using [hN])⟩
  refine wp_countdown (cnt := .rcx) (N := N / 8) (by omega_using [hN]) (by omega_using [hN0, h8]) (fun k s' =>
      s'.gpr .rsi = a + BitVec.ofNat 64 (8 * k) ∧ s'.gpr .rdi = b + BitVec.ofNat 64 (8 * k) ∧
      (s'.gpr .rdx = 0 ↔ bytesAt s.mem a (8 * k) = bytesAt s.mem b (8 * k)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', hdx', hm', hrd', hwr', kk⟩ _ => ?_)
    (fun _ ⟨_, _, h1, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, by rwa [show 8 * (N / 8) = N by omega_using [h8]] at h1, h5⟩)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [hdx]; simp [bytesAt], rfl, rfl, rfl, Keep.refl _ _⟩ hcx
  refine WP.mono (cmpBody_ok s' (by rw [hrd', hwr', hsi']; exact in8 ha k hk)
    (by rw [hrd', hwr', hdi']; exact in8 hb k hk)) fun s'' ⟨⟨hm, hdx, hsi'', hdi'', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hsi'', hsi', show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
        by rw [hdi'', hdi', show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl, ?_, hm.trans hm',
        k'.2.1.trans hrd', k'.2.2.trans hwr', (kk.trans k').mono (by decide)⟩, hcx, hz⟩
  rw [hdx, or_xor_eq_zero, hdx', hsi', hdi', hm', show 8 * (k + 1) = 8 * k + 8 by omega_using [], bytesAt_eq_succ8]

theorem sel_ok (s : State) {g kb key : Addr} (e : Bool) (hg : InRegions (s.rd ++ s.wr) g 32)
    (hkb : InRegions (s.rd ++ s.wr) kb 32) (hkey : InRegions s.wr key 32)
    (dg : Region.Disjoint ⟨g, 32⟩ ⟨key, 32⟩) (dkb : Region.Disjoint ⟨kb, 32⟩ ⟨key, 32⟩)
    (hsi : s.gpr .rsi = g) (hdi : s.gpr .rdi = kb) (h8 : s.gpr .r8 = key)
    (hax : s.gpr .rax = if e then BitVec.allOnes 64 else 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 32) :
    WP isa (.loop selBody .ne) s fun s' =>
      bytesAt s'.mem key 32 = (if e then bytesAt s.mem g 32 else bytesAt s.mem kb 32) ∧
      Frame [⟨key, 32⟩] s.mem s'.mem ∧ Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.mono (wp_countdown (cnt := .rcx) (N := 32) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = g + BitVec.ofNat 64 k ∧ s'.gpr .rdi = kb + BitVec.ofNat 64 k ∧
      s'.gpr .r8 = key + BitVec.ofNat 64 k ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨key, 32⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (key + BitVec.ofNat 64 j) =
        if e then s.mem (g + BitVec.ofNat 64 j) else s.mem (kb + BitVec.ofNat 64 j)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', h8', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [h8]; simp, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), Keep.refl _ _⟩ hcx) fun s' ⟨_, _, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have hax' : s'.gpr .rax = if e then BitVec.allOnes 64 else 0 := by rw [kk.gpr (by decide)]; exact hax
    refine WP.mono (selBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte hg hk (by omega_using []))
      (by rw [hrd', hwr', hdi']; exact inRegions_byte hkb hk (by omega_using []))
      (by rw [hwr', h8']; exact inRegions_byte hkey hk (by omega_using [])))
      fun s'' ⟨⟨hm, hax'', hsi'', hdi'', h8'', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [h8'', h8', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, h8']
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega_using [hk]) (by omega_using []))
    · have eg : s'.mem (g + BitVec.ofNat 64 k) = s.mem (g + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨g, 32⟩) (by simpa using dg) (show 32 ≤ 2 ^ 64 by decide) hk
      have ekb : s'.mem (kb + BitVec.ofNat 64 k) = s.mem (kb + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨kb, 32⟩) (by simpa using dkb) (show 32 ≤ 2 ^ 64 by decide) hk
      rw [hm, h8', writeW8_apply]
      by_cases ej : j = k
      · subst ej
        rw [ifp rfl, hsi', hdi', hax', sel_byte, eg, ekb]
      · rw [ifn (fun h => ej (by have := congrArg BitVec.toNat h; simp at this; omega_using [hk, hj, this])), hc j (by omega_using [hj, ej])]
  · cases e
    · simp only [bytesAt, Bool.false_eq_true, ite_false]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)
    · simp only [bytesAt, ite_true]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)

/-! ## The choice -/

abbrev setupB (o n : Nat) : List Instr := [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx),
  .alu .add .rdi (.imm (BitVec.ofNat 32 o)), .mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8))), .mov32 .rdx (.imm 0)]

theorem setup_ok {o n : Nat} (ho : o < 2 ^ 31) (hn : n < 2 ^ 32) (s : State) :
    WP isa (.block (setupB o n)) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rsi = pa s (.r14, 0) ∧ s'.gpr .rdi = pa s (sc o) ∧
        s'.gpr .rcx = BitVec.ofNat 64 (n / 8) ∧ s'.gpr .rdx = 0) ∧
      Keep [.rsi, .rdi, .rcx, .rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat ho, sw_ofNat (show n / 8 < 2 ^ 32 by omega_using [hn])]
  rw [pa, add_ofNat_zero]

theorem select_ok {o n : Nat} (ho : o < 2 ^ 31) (hn : n < 2 ^ 32) (hn0 : 0 < n) (h8 : n % 8 = 0)
    {s : State}
    (hc : InRegions (s.rd ++ s.wr) (pa s (.r14, 0)) n)
    (hct : InRegions (s.rd ++ s.wr) (pa s (sc o)) n) (hg : InRegions (s.rd ++ s.wr) (pa s (sc oG)) 32)
    (hkb : InRegions (s.rd ++ s.wr) (pa s (sc oKB)) 32) (hkey : InRegions s.wr (pa s (.r12, 0)) 32)
    (dg : Region.Disjoint ⟨pa s (sc oG), 32⟩ ⟨pa s (.r12, 0), 32⟩)
    (dkb : Region.Disjoint ⟨pa s (sc oKB), 32⟩ ⟨pa s (.r12, 0), 32⟩) :
    WP isa (selectAt o n) s fun s' => PPost s s' [((.r12, 0), 32)] ∧
      bytesAt s'.mem (pa s (.r12, 0)) 32 =
        if bytesAt s.mem (pa s (.r14, 0)) n = bytesAt s.mem (pa s (sc o)) n then
          bytesAt s.mem (pa s (sc oG)) 32 else bytesAt s.mem (pa s (sc oKB)) 32 := by
  unfold selectAt
  refine WP.seq (WP.mono (setup_ok ho hn s) fun s₁ ⟨⟨hm₁, hsi₁, hdi₁, hcx₁, hdx₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₁ hn hn0 h8 (by rw [k₁.2.1, k₁.2.2]; exact hc) (by rw [k₁.2.1, k₁.2.2]; exact hct) hsi₁ hdi₁
    hdx₁ hcx₁) fun s₂ ⟨hm₂, hrd₂, hwr₂, hdx₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok s₂) fun s₃ ⟨⟨hm₃, hax₃, hsi₃, hdi₃, h8₃, hcx₃⟩, k₃⟩ => ?_)
  have e12 : ∀ r ∈ [Reg.rbx, Reg.r12], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide),
      k₁.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have pG : pa s₂ (sc oG) = pa s (sc oG) := by rw [pa, pa, e12 .rbx (by simp)]
  have pKB : pa s₂ (sc oKB) = pa s (sc oKB) := by rw [pa, pa, e12 .rbx (by simp)]
  have pK : pa s₂ (.r12, 0) = pa s (.r12, 0) := by rw [pa, pa, e12 .r12 (by simp)]
  rw [pG] at hsi₃; rw [pKB] at hdi₃; rw [pK] at h8₃
  have hmem : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have hrd : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.2.1, k₃.2.2, hrd₂, hwr₂, k₁.2.1, k₁.2.2]
  have hwr : s₃.wr = s.wr := by rw [k₃.2.2, hwr₂, k₁.2.2]
  have hax : s₃.gpr .rax = if decide (bytesAt s.mem (pa s (.r14, 0)) n = bytesAt s.mem (pa s (sc o)) n) then
      BitVec.allOnes 64 else 0 := by
    rw [hax₃]
    rw [hm₁] at hdx₂
    exact ite_congr (propext (hdx₂.trans decide_eq_true_iff.symm)) (fun _ => rfl) (fun _ => rfl)
  refine WP.mono (sel_ok s₃ _ (by rw [hrd]; exact hg) (by rw [hrd]; exact hkb) (by rw [hwr]; exact hkey) dg dkb hsi₃
    hdi₃ h8₃ hax hcx₃) fun s₄ ⟨hb, hf, k₄⟩ => ⟨?_, ?_⟩
  · refine post_of_keep ((((k₁.trans k₂).trans k₃).trans k₄).mono (rs' := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10])
      (by decide)) (by decide) ?_
    rw [← hmem]; exact hf
  · rw [hb, hmem]
    simp only [decide_eq_true_eq]

end Decaps

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation

After K-PKE.Decrypt (`DcDec.lean`): `G(m' ‖ h)` and `J(z ‖ c)` (`hashes_ok`),
K-PKE.Encrypt in the context `dcX` (which keeps `K'` and `K̄`), and the choice
of the key (`select_okD`). The function returns 1 with
`ML-KEM.Decaps_internal(dk, c)` in `key` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`kemDecaps_correct`); it leaks
only the pointers and `ρ` (`kemDecaps_ct`). Each parameter set's file moves
this to its shared contract.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcM' (L : Kem) (σ : State) : List Byte := KPke.decM L.p (dcDk L σ) (dcC L σ)
abbrev dcG (L : Kem) (σ : State) : List Byte × List Byte := G (dcM' L σ ++ KPke.dkH L.p (dcDk L σ))
abbrev dcKb (L : Kem) (σ : State) : List Byte := J (KPke.dkZ L.p (dcDk L σ) ++ dcC L σ)
abbrev dcEk (L : Kem) (σ : State) : List Byte := KPke.dkEk L.p (dcDk L σ)

/-- What `K-PKE.Encrypt` keeps: `DC`, `K'` at `G` and `K̄` at `KB`. -/
structure DCK (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG L σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = dcKb L σ

theorem DCK.step {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s s' : State} (h : DCK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : dckChk L ws = true) : DCK L σ s' := by
  simp only [dckChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.k, by rw [L₀.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcX {oc : Nat} (W : DcWfB L oc) (σ : State) : Ctx (dcR L) (dcW L) where
  Out s := (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcXA {oc : Nat} (W : DcWfB L oc) : Ctx (dcR L) (dcW L) where
  Out s := ∃ σ, (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay := fun ⟨_, hp, h⟩ => h.dc.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

theorem shakeSuffix31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {oc : Nat} (W : DcWfB L oc) (σ s : State) : Prop :=
  Enc.EIn L (dcX W σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s : State} (h : DM L σ s) :
    WP isa (hashes L) s (EncI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * L.k + 96 = L.dkLen := rfl
  unfold hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * L.k + 32 + 32 ≤ L.dkLen by omega_using [hdk]), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136)
    (out := sc oKB) (len := 32) W.h₂ (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    slice_of k₁.dk (show 768 * L.k + 64 + 32 ≤ L.dkLen by omega_using [hdk]), shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (dcM' L σ ++ KPke.dkH L.p (dcDk L σ)) := by
    rw [L₁.keepBytes hP₂.b W.h₂G]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (dcG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (dcG L σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, slice_of k₂.dk (show 384 * L.k + (384 * L.k + 32) ≤ L.dkLen by omega_using [hdk]), ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₂.b W.h₂M, L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (W : DcWf L) (σ s : State) : Prop :=
  Enc.EOut L (dcX W.toDcWfB σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s

/-- At the end: `r15` as `allOk`, and the key if it is 1. -/
structure DEnd (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) then 1 else 0
  key : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (.r12, 0)) 32 =
    if dcC L σ = KPke.ct L.p (aHat (Enc.rhoE L (dcEk L σ))) (dcEk L σ) (dcM' L σ) (dcG L σ).2 then (dcG L σ).1
    else dcKb L σ

/-- Before the choice of the key: what `K-PKE.Encrypt` keeps, `r15` as
`allOk`, and `c'` at `scratch + oc` if it is 1. -/
structure SelIn (L : Kem) (oc : Nat) (σ s : State) : Prop where
  pre : (decapsK L).pre σ
  k : DCK L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) then 1 else 0
  ct : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (sc oc)) L.ctLen =
    KPke.ct L.p (aHat (Enc.rhoE L (dcEk L σ))) (dcEk L σ) (dcM' L σ) (dcG L σ).2

theorem EncO.sel {W : DcWf L} {σ s : State} (h : EncO W σ s) : SelIn L L.oCT σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

theorem select_okD {oc : Nat} (W : DcWfB L oc) {σ : State} {s : State} (h : SelIn L oc σ s) :
    WP isa (selectAt oc L.ctLen) s (DEnd L σ) := by
  have hp := h.pre
  have k := h.k
  have L₀ := k.dc.lay W hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB (dcB L) p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L₀.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain ⟨i1, i2, i3, i4, i5, s1, s2⟩ := W.sel
  refine WP.mono (select_ok W.ct.1 W.ct.2.1 W.ct.2.2.1 W.ct.2.2.2 (cR i1) (cR i2) (cR i3) (cR i4)
    (L₀.cW i5 _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) (L₀.disj s1) (L₀.disj s2))
    fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step W hp hP.b W.selK, by rw [hP.cs .r15 (by decide)]; exact h.r15, fun ho => ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.ct ho])) (fun _ => k.k) (fun _ => k.kb)

theorem DEnd.hin {oc : Nat} (W : DcWfB L oc) {σ s : State} (hp : (decapsK L).pre σ) (h : DEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.dc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the key. -/
theorem post_of {oc : Nat} (W : DcWfB L oc) {σ s : State} (h : DEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (decapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.dc.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := aHat (Enc.rhoE L (dcEk L σ)))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, h.key ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

theorem decrypt_ok {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ : State}
    (hp : (decapsK L).pre σ) {s : State} (h : DC L σ s) (h15 : s.gpr .r15 = 1) : WP isa (decrypt L A) s (DM L σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L k 0 σ) L.k 0 (fun k _ hk s hs => u_ok A W K hp (by omega_using [hk]) hs) s
    (DR.zero h h15)) fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L L.k k σ) L.k 0 (fun k _ hk s hs => s_ok hA W hp (by omega_using [hk]) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact tail_ok hA W K hp h₂

end Decaps

open Decaps in
theorem kemDecaps_correct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    (hctl : ctlOk (kemDecaps L v.callee) = true) (σ : State) (hp : (decapsK L).pre σ) :
    ∃ t s', Exec isa (kemDecaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (decapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (decrypt_ok v.arith W K hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashes_ok W.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc.encrypt_ok v K W.toKemWf (C := dcX W.toDcWfB σ) W.enc h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (select_okD W.toDcWfB (EncO.sel (W := W) h₄)) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin W.toDcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toDcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (decapsK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

theorem rho_pub {σ₁ σ₂ : State} (pub : (decapsK L).pub σ₁ σ₂) : Enc.rhoE L (dcEk L σ₁) = Enc.rhoE L (dcEk L σ₂) := by
  rw [Enc.rhoE, Enc.rhoE, KPke.ekRho_dkEk, KPke.ekRho_dkEk]; exact pub.2.2.2.2.2

theorem decrypt_tr {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L fun σ s => DC L σ s ∧ s.gpr .r15 = 1) (decrypt L A) fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => R L (DR L k 0)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => u_ok A W K hp (by omega_using [hk]) hs) (u_tr A W K (by omega_using [hk])))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, DR.zero h₁.1 h₁.2, DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L (DR L L.k k)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => s_ok hA W hp (by omega_using [hk]) hs) (s_tr hA W (by omega_using [hk]))) ?_
  rw [Nat.zero_add]
  exact tail_tr hA W K

theorem hashes_trL {oc : Nat} (W : DcWfB L oc) : RelCT isa (LRel (dcR L) (dcW L)) (hashes L) fun _ _ => True := by
  unfold hashes
  exact RelCT.seq (LRel.step (dcB_bases L) (hash_tr (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)])
      (rate := 72) (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72) (out := sc oG)
        (len := 64) W.h₁ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136) (out := sc oKB)
      (len := 32) W.h₂ (show 0x1f < 256 by decide))

theorem hashes_tr {oc : Nat} (W : DcWfB L oc) : RelCT isa (R L (DM L)) (hashes L) fun _ _ => True :=
  rel2_of (hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

theorem EIn.any {oc : Nat} {W : DcWfB L oc} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : Enc.EIn L (dcX W σ) E ek m r s) : Enc.EIn L (dcXA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (EncI W.toDcWfB)) (encrypt L v.callee (.rbp, 384 * L.k)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR L) (dcW L) x y ∧
      Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) ρ x ∧ Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := dcXA W.toDcWfB) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (dcEk L σ₁), dc_lrel W.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

theorem select_tr {oc : Nat} (W : DcWfB L oc) :
    RelCT isa (R L (SelIn L oc)) (selectAt oc L.ctLen) fun _ _ => True := by
  obtain ⟨_, selT⟩ := W.selT
  exact rel2_of (Q := LRel (dcR L) (dcW L)) (taintRel [.rbx, .r12, .r14] (fun _ _ h =>
    fa3 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2)) selT)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.k.dc h₂.k.dc

theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (R L (DEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .rcx) (by decide), h₂.dc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end Decaps

open Decaps in
theorem kemDecaps_ct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    ConstantTime isa (decapsK L).pre (decapsK L).pub (kemDecaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecaps
  refine RelCT.seq (relInv (I' := fun σ s => DC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM L) (fun σ s hp hs => decrypt_ok v.arith W K hp hs.1 hs.2)
    (decrypt_tr v.arith W K)) ?_
  refine RelCT.seq (relInv (I' := EncI W.toDcWfB) (fun σ s hp hs => hashes_ok W.toDcWfB hp hs) (hashes_tr W.toDcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.toKemWf (C := dcX W.toDcWfB σ) W.enc hs.1 hs.2)
    (encrypt_tr v W K)) ?_
  refine RelCT.seq (relInv (I' := DEnd L) (fun σ s _ hs => select_okD W hs.sel)
    (RelCT.mono (select_tr W.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩)
      fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkFusedCT16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, with 16-bit polynomials, constant time

As `EkFusedCT.lean`, for `kemEncaps16` (`kemEncaps16_ct`): two runs whose
pointers and `ρ` agree leak the same, the fragments' blocks of `pad(ek)` and
the sponge's state, which only the fourth Keccak state absorbs, at fixed
addresses, and K-PKE.Encrypt with 16-bit polynomials for the same `ρ`
(`Enc16.rest_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace EkF16

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases EcWfB trL)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs ekG ProOut R ek_lrel rho_pub)
open VG.Proof.MlKem.X86_64.EkF (relFalse)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero matH hblk frag)

variable (K : Kem16)

/-- The taint checks of the pieces the fused encapsulation adds, from the pointers. -/
structure EkT16Wf : Prop where
  rT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oSB) (.r14, 384 * K.L.k) 32) h).isSome = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (.block (hzero K)) h).isSome = true
  hT : ∀ i < nb K.L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (hblk K i) h).isSome = true
  hcT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oH) (sc (oHS K)) 32) h).isSome = true
  ij : ∀ i < nb K.L, ∀ J < 4, (3 * i + J) / K.L.k < 4 ∧ (3 * i + J) % K.L.k < 4

variable {K}

section
variable (F : Ek16HWf K) (T : EkT16Wf K)
include F T

theorem rho16_tr : RelCT isa (R K.L (ProOut K.L)) (copy (sc oSB) (.r14, 384 * K.L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.rT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

theorem hz16_tr : RelCT isa (R K.L (RI16 K)) (.block (hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

theorem hcopy16_tr : RelCT isa (R K.L fun σ s => FI16 K σ (nb K.L) s) (copy (sc oH) (sc (oHS K)) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.hcT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

end

/-- Before fragment `i`, for the `ρ` of `ek`. -/
abbrev FIρ16 (K : Kem16) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (encK K.L).pre σ ∧ FI16 K σ i s ∧ Enc.rhoE K.L (ekE K.L σ) = ρ

theorem frag16_tr (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) {i : Nat} (hi : i < nb K.L) :
    RelCT isa (R K.L fun σ s => FI16 K σ i s) (frag K b i) fun _ _ => True := by
  have W := F.toEcWfB
  obtain ⟨_, t⟩ := T.hT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  have hin : inB (ecB K.L) (sc 0) 136 = true := by
    simp only [s4_16Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧ FIρ16 K ρ i x ∧ FIρ16 K ρ i y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FIρ16 K ρ i x → WP isa (hblk K i) x fun x' =>
        PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (hblk16_ok F.toEk16FWf hp hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep W hp hP h15 hc.2).sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trL W t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ (ecR K.L) (ecW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (ecB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 0) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 1) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 2) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 3) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq W.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec, ⟨σ₁, p₁, h₁, rfl⟩,
      ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem frags16_tr (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L fun σ s => FI16 K σ 0 s) (seqR (frag K b) 0 (nb K.L)) (R K.L fun σ s => FI16 K σ (nb K.L) s) := by
  have := seqR_tr (R := fun i => R K.L fun σ s => FI16 K σ i s) (nb K.L) 0 fun k _ hk =>
    relInv (fun σ s hp h => frag16_ok F.toEk16FWf hB hp (by omega_using [hk]) h) (frag16_tr F T hB (by omega_using [hk]))
  rwa [Nat.zero_add] at this

theorem quadM16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) {q : Nat} (hq : q < K.L.k * K.L.k / 4) (h3 : 3 * nb K.L ≤ 4 * q) :
    RelCT isa (R K.L fun σ s => MI16 K σ (4 * q) s) (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW))
      fun _ _ => True := by
  have W := F.toEcWfB
  have hc := F.qC q hq h3
  simp only [Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hk4 := W.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (ecR K.L) (ecW K.L) ρ K.L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad16_tr (ρ := ρ) v (ecB_bases K.L) (by omega_using [hq, h16])
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this],
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this]⟩) hc.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsM16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s => MI16 K σ (3 * nb K.L) s) (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L))
      (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) := by
  have := ents16_tr (n, c) K.L.k K.oA (sc K.oW) (R := fun e => R K.L fun σ s => 3 * nb K.L ≤ e ∧ MI16 K σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega_using [he, he', h3]))
    (fun q hq => if h3 : 3 * nb K.L ≤ 4 * q then
        relInv (fun σ s hp hs => WP.mono (quadM16_ok v F hp hq hs.1 hs.2) fun _ h => ⟨by omega_using [h3], h⟩)
          (RelCT.mono (quadM16_tr v F hq h3)
            (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h)
      else relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3', _⟩, _⟩ => h3 h3')
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega_using [this]) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matH16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L (ProOut K.L)) (matH K (n, c) b) (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) := by
  unfold matH
  exact RelCT.seq (relInv (I' := RI16 K) (fun σ s hp h => rho16_ok F hp h) (rho16_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FI16 K σ 0 s) (fun σ s hp h => hz16_ok F hp h) (hz16_tr F T))
      (RelCT.seq (frags16_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => MI16 K σ (3 * nb K.L) s) (fun σ s hp h => hcopy16_ok F hp h) (hcopy16_tr F T))
          (entsM16_tr v F))))

theorem hashesF16_tr (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) EncapsH.hashes fun _ _ => True :=
  rel2_of (Encaps.hashes_trL F.toEcWfB) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

/-- The rest of K-PKE.Encrypt if every `SampleNTT` succeeded, for a given `ρ`. -/
theorem ifRest16ρ_tr (hK : KpkeOk K.L) (v : Sample4Impl) {rbs wbs : List (Reg × Nat)} {C : Ctx rbs wbs}
    (hk : K.L.k ≤ 4) (hc : Enc16.EncChks K (rbs ++ wbs) wbs C.chk (.r14, 0))
    (ht : Enc16.tailChk K (rbs ++ wbs) wbs C.chk (.r14, 0) (.r13, 0) = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Enc16.EBρ K C (.r14, 0) ρ (K.L.k * K.L.k) x ∧
        Enc16.EBρ K C (.r14, 0) ρ (K.L.k * K.L.k) y)
      (ifOk (Top16.encRest K v.callee (.r14, 0) (.r13, 0))) fun _ _ => True := by
  refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (Enc16.rest_tr hK v (show Reg.r14 ∉ argRegs by decide) (by decide) hk hc ht (ρ := ρ)) ?_
      fun _ _ _ => trivial) fun _ _ _ => trivial
  rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
  have o₁ := KeyGen.r15_ne h₁.m.r15 hne
  have o₂ : allOk K.L.k (Enc.rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
  exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc16.ER0.start (h₁.flag hx hc) o₁⟩,
    ⟨ek₂, m₂, r₂, e₂, Enc16.ER0.start (h₂.flag hy hc) o₂⟩⟩

theorem ifRest16_tr (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s =>
        Enc16.EB16 K (Ek.ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ) (ekG K.L σ).2 (K.L.k * K.L.k) s)
      (ifOk (Top16.encRest K v.callee (.r14, 0) (.r13, 0))) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧
      Enc16.EBρ K (Ek.ekCA F.toEcWfB) (.r14, 0) ρ (K.L.k * K.L.k) x ∧
      Enc16.EBρ K (Ek.ekCA F.toEcWfB) (.r14, 0) ρ (K.L.k * K.L.k) y)
    (Q := fun _ _ => True) fun ρ => ifRest16ρ_tr hK v (C := Ek.ekCA F.toEcWfB) F.k.2 F.enc F.tl) ?_
    fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel F.toEcWfB p₁ p₂ pub h₁.i.out.2.ec h₂.i.out.2.ec,
    ⟨_, _, _, rfl, Ek.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Ek.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

theorem out16_tr (F : Ek16HWf K) :
    RelCT isa (R K.L (EncO16 F)) (copy (.r12, 0) (sc oG) 32) fun _ _ => True := by
  obtain ⟨_, oT₁⟩ := F.oT₁
  exact rel2_of (trL F.toEcWfB oT₁) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ek_lrel F.toEcWfB p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec

end EkF16

open EkF16 Ek in
theorem kemEncaps16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) (T : EkT16Wf K)
    {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b) :
    ConstantTime isa (encK K.L).pre (encK K.L).pub (kemEncaps16 K v.callee (n, c) b) := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps16
  refine RelCT.seq (relInv (I' := ProOut K.L) (fun σ s hp hs => by subst hs; exact pro_ok F.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (matH16_tr hS F T hB) ?_
  refine RelCT.seq (relInv (I' := fun σ s => Enc16.EB16 K (ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ)
    (ekG K.L σ).2 (K.L.k * K.L.k) s) (fun σ s hp hs => hashesF16_ok F hp hs) (hashesF16_tr F)) ?_
  refine RelCT.seq (relInv (I' := EncO16 F) (fun σ s _ hs => ifRest16_ok hK v F hs) (ifRest16_tr hK v F)) ?_
  refine RelCT.seq (relInv (I' := EKEnd K.L) (fun σ s _ hs => out16_ok F hs) (out16_tr F)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DjFusedCT16`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.DjFused16`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.DcTop16`, which only this module used -/

section

/-!
# ML-KEM on x86-64: the end of decapsulation's re-encryption, with 16-bit polynomials

The state after the re-encryption with 16-bit polynomials (`Enc16.lean`)
writes `c'` to `oCT16` (`EncO16`), the input of the choice of the key
(`EncO16.sel`), for `kemDecapsJ16_correct` (`DjFused16.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

/-- The end of the re-encryption. -/
abbrev EncO16 {K : Kem16} (W : Dc16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (dcX W.toDcWfB σ) (sc oCT16) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s

theorem EncO16.sel {K : Kem16} {W : Dc16Wf K} {σ s : State} (h : EncO16 W σ s) : SelIn K.L oCT16 σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

end Decaps16

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DjFrag16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, the fragments

As `EkFrag16.lean`, for `kemDecapsJ16`'s fragments (`DecapsJ16.frag`):
before them, decapsulation knows `K'` at `G` but not yet `K̄`, so the
inputs of the re-encryption (`Enc16.EB16`) are in the context `dcXG`, which
keeps `DC` and `K'` (`DCG`). Each fragment copies 408 bytes of
`pad(z ‖ c)` (suffix `0x1f`, `hbE`) to `HB`: the first from `z` and the
start of `c`, the others from `c`, the last followed by the padding
(`jblk_ok`); the sponge's state is `hstate (z ‖ c) (3i) 0x1f` before
fragment `i` (`FJ`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.DjF16

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.MlKem.X86_64.Decaps (DC dcDk dcC dcEk dcM' dcG dcKb dcR dcW dcB dcB_bases dcChk DcWfB slice_of)
open VG.Proof.MlKem.HSponge (hstate)
open VG.Proof.MlKem.X86_64.EkF (blk Partial stateAt_keep hbE hbE_blk habs_blk habs_congr)
open VG.Proof.MlKem.X86_64.EkF16 (padTail16_ok)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB padTail)
open VG.Impl.MlKem.X86_64.DecapsJ16 (jLen jblk frag)
open VG.Impl.MlKem.X86_64.Top16 (aP)

/-! ## The context before `K̄` -/

/-- A piece writing `ws` keeps `DC` and `K'`. -/
def dcgChk (L : Kem) (ws : List (Ptr × Nat)) : Bool := dcChk L ws && keepB (dcB L) ws (sc oG) 32

/-- `DC`, and `K'` at `G`. -/
structure DCG (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG L σ).1

theorem DCG.step {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s s' : State}
    (h : DCG L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : dcgChk L ws = true) : DCG L σ s' := by
  simp only [dcgChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1, by rw [L₀.keepBytes hP hc.2]; exact h.k⟩

/-- The context of the re-encryption's inputs before `K̄`, in a run from `σ`. -/
def dcXG {L : Kem} {oc : Nat} (W : DcWfB L oc) (σ : State) : Ctx (dcR L) (dcW L) where
  Out s := (decapsK L).pre σ ∧ DCG L σ s
  chk := dcgChk L
  bs := dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- `z ‖ c`. -/
abbrev zcE (L : Kem) (σ : State) : List Byte := KPke.dkZ L.p (dcDk L σ) ++ dcC L σ

theorem zcE_length (L : Kem) (σ : State) : (zcE L σ).length = 32 + L.ctLen := by
  simp only [zcE, List.length_append, KPke.dkZ, List.length_take, List.length_drop, dcDk, dcC, bytesAt_length]
  have : L.dkLen = 768 * L.p.k + 96 := rfl
  omega_using [this]

/-! ## The checks of the layout -/

variable (K : Kem16)

/-- A piece writing `ws` keeps the re-encryption's inputs, `ρ` at `SB` and the first `e` entries of `Â`. -/
def fkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool :=
  Enc.inKeep K.L (dcB K.L) (dcgChk K.L) (.rbp, 384 * K.L.k) ws && keepB (dcB K.L) ws (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (dcB K.L) ws (aP K e') 512

/-- ... and the sponge's state. -/
def hkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool := fkeep K ws e && keepB (dcB K.L) ws (sc (oHS K)) 200

/-- The blocks of fragment `i`. -/
def jbChk (i : Nat) : Bool :=
  (if i = 0 then
      copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.rbp, 768 * K.L.k + 64) 32 &&
        copyChk (dcB K.L) (dcW K.L) (sc (oHB K + 32)) (.r14, 0) 376 &&
        keepB (dcB K.L) [(sc (oHB K), 32)] (.r14, 0) K.L.ctLen &&
        keepB (dcB K.L) [(sc (oHB K + 32), 376)] (sc (oHB K)) 32
    else if 408 * i + 408 ≤ jLen K then copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.r14, 408 * i - 32) 408
    else copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.r14, 408 * i - 32) (jLen K - 408 * i) &&
      inB (dcW K.L) (sc (oHB K)) 408 &&
      keepB (dcB K.L) [(sc (oHB K + (jLen K - 408 * i)), 408 - (jLen K - 408 * i))] (sc (oHB K)) (jLen K - 408 * i)) &&
  hkeep K [(sc (oHB K), 408)] (3 * i)

/-- The seeds of fragment `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (dcB K.L) (dcW K.L) J && hkeep K (seedW J) (3 * i) &&
    keepB (dcB K.L) (seedW J) (sc (oHB K)) 408

/-- The fragment inlined, of fragment `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (dcB K.L) (dcW K.L) (K.oA + 512 * (3 * i)) K.oW &&
    fkeep K [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)] (3 * i)

/-- What the fragments need of the layout, evaluated for each parameter set. -/
structure DjFWf : Prop extends Decaps16.Dc16Wf K where
  part : 0 < jLen K % 136 ∧ jLen K % 136 < 135
  nbJ : 3 * nb K.L = jLen K / 136 + 1
  nbK : 1 < nb K.L ∧ 3 * nb K.L ≤ K.L.k * K.L.k
  last : 272 < jLen K - 408 * (nb K.L - 1) ∧ jLen K - 408 * (nb K.L - 1) < 406 ∧ jLen K < 408 * nb K.L
  len8 : jLen K % 8 = 0 ∧ jLen K < 2 ^ 20
  rC : (copyChk (dcB K.L) (dcW K.L) (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32 &&
    Enc.inKeep K.L (dcB K.L) (dcgChk K.L) (.rbp, 384 * K.L.k) [(sc oSB, 32)]) = true
  zC : (inB (dcW K.L) (sc (oHS K)) 200 && fkeep K [(sc (oHS K), 200)] 0) = true
  jb : ∀ i < nb K.L, jbChk K i = true
  sd : ∀ i < nb K.L, sdChk K i = true
  sm : ∀ i < nb K.L, smChk K i = true

/-! ## What holds before each fragment -/

variable {K}

/-- The re-encryption's inputs in the context before `K̄`, with the first `e` entries of `Â`. -/
abbrev EBG (W : DcWfB K.L oCT16) (σ : State) (e : Nat) (s : State) : Prop :=
  Enc16.EB16 K (dcXG W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 e s

/-- Before fragment `i`. -/
structure FJ (W : DcWfB K.L oCT16) (σ : State) (i : Nat) (s : State) : Prop where
  eb : EBG W σ (3 * i) s
  hs : stateAt s.mem (pa s (sc (oHS K))) = hstate (zcE K.L σ) (3 * i) (BitVec.ofNat 8 0x1f)

/-- A piece that writes `ws` and keeps `r15` keeps `FJ`. -/
theorem FJ.keep {W : DcWfB K.L oCT16} {σ : State} {i : Nat} {s s' : State} (h : FJ W σ i s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15)
    (hc : hkeep K ws (3 * i) = true) : FJ W σ i s' := by
  simp only [hkeep, fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := (dcXG W σ).lay h.eb.i.out
  exact ⟨⟨h.eb.i.keep hP hE, by rw [L₀.keepBytes hP hS]; exact h.eb.sb,
    ⟨by rw [h15]; exact h.eb.m.r15, fun e he f hf => L₀.keepPoly16 hP (hA e he) (h.eb.m.mat e he f hf)⟩⟩,
    by rw [stateAt_keep L₀ hP hH]; exact h.hs⟩

theorem dkZ_length (L : Kem) (σ : State) : (KPke.dkZ L.p (dcDk L σ)).length = 32 := by
  simp only [KPke.dkZ, List.length_take, List.length_drop, dcDk, bytesAt_length]
  have : L.dkLen = 768 * L.p.k + 96 := rfl
  omega_using [this]

theorem zc_drop (L : Kem) (σ : State) {n : Nat} (hn : 32 ≤ n) : (zcE L σ).drop n = (dcC L σ).drop (n - 32) := by
  rw [zcE, List.drop_append, List.drop_eq_nil_of_le (by rw [dkZ_length]; omega_using [hn]), List.nil_append, dkZ_length]

theorem jblk_ok (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State} (h : FJ F.toDcWfB σ i s) :
    WP isa (jblk K i) s fun s' => PPostB s s' [(sc (oHB K), 408)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f) := by
  have L₀ := (dcXG F.toDcWfB σ).lay h.eb.i.out
  have dc := h.eb.i.out.2.dc
  have hc := F.jb i hi
  have hzl : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  have hdk : 768 * K.L.k + 96 = K.L.dkLen := rfl
  have hl := F.last
  have hn := F.nbJ
  have hk := F.nbK
  have h8 := F.len8
  have hcl : jLen K = 32 + K.L.ctLen := rfl
  unfold jblk
  unfold jbChk at hc
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte, Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨⟨hz, hcc⟩, hkc⟩, hkz⟩, -⟩ := hc
    refine WP.seq (WP.mono (copy_okL L₀ (show Reg.rbp ≠ .rdi by decide) hz) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
    have L₁ := L₀.post hP₁.b (dcB_bases K.L)
    refine WP.mono (copy_okL L₁ (show Reg.r14 ≠ .rdi by decide) hcc) fun s₂ ⟨hP₂, hb₂⟩ => ?_
    have e : pa s (sc (oHB K + 32)) = pa s (sc (oHB K)) + BitVec.ofNat 64 32 := (off_add _ _ _).symm
    have p₁ : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun _ => hP₁.pa rbx_cs
    have p₂ : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun _ => hP₂.pa rbx_cs
    have r₁ : pa s₁ (.r14, 0) = pa s (.r14, 0) := hP₁.pa (by decide)
    have hP : PPost s s₂ [(sc (oHB K), 408)] := by
      refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
        (ws := [(sc (oHB K), 32), (sc (oHB K + 32), 376)])
        (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
        (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Region.sub_prefix (by omega_using [])
      · show Region.Sub ⟨pa s (sc (oHB K + 32)), _⟩ ⟨pa s (sc (oHB K)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega_using [])
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have A : bytesAt s₂.mem (pa s (sc (oHB K))) 32 = KPke.dkZ K.L.p (dcDk K.L σ) := by
      have k₁ := L₁.keepBytes hP₂.b hkz
      rw [p₂, p₁] at k₁
      rw [k₁, hb₁, slice_of dc.dk (show 768 * K.L.k + 64 + 32 ≤ K.L.dkLen by omega_using [hdk])]
      rfl
    have B : bytesAt s₂.mem (pa s (sc (oHB K + 32))) 376 = (dcC K.L σ).take 376 := by
      have kc := L₀.keepBytes hP₁.b hkc
      rw [r₁, dc.c] at kc
      rw [← p₁, hb₂, r₁, ← bytesAt_take _ _ (show 376 ≤ K.L.ctLen by omega), kc]
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) 32 376
    rw [← e, A, B] at sp
    rw [sp, hbE, ite_eq_left (show 408 * 0 + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hl, hk]), Nat.mul_zero, List.drop_zero, zcE,
      List.take_append, List.take_of_length_le (l := KPke.dkZ K.L.p (dcDk K.L σ)) (by rw [dkZ_length]; omega_using []),
      dkZ_length]
  · simp only [h0, ↓reduceIte] at hc ⊢
    have h32 : 32 ≤ 408 * i := by omega_using [h0]
    by_cases hf : 408 * i + 408 ≤ jLen K
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
        ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      rw [hb, slice_of dc.c (show 408 * i - 32 + 408 ≤ K.L.ctLen by omega_using [hl, hcl, hf]), hbE,
        ite_eq_left (show 408 * i + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hf]), zc_drop K.L σ h32]
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
      have hii : i = nb K.L - 1 := by omega_using [hi, hl, hf]
      have hlen : 272 < jLen K - 408 * i ∧ jLen K - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
      have hm8 : (jLen K - 408 * i) % 8 = 0 := by omega_using [h8]
      refine WP.seq (WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
      have L₁ := L₀.post hP₁.b (dcB_bases K.L)
      refine WP.mono (padTail16_ok K L₁ hlen.2 hm8 hin (d := 0x1f) (by decide)) fun s₂ ⟨hP₂, hb₂⟩ => ?_
      have e : pa s (sc (oHB K + (jLen K - 408 * i))) = pa s (sc (oHB K)) + BitVec.ofNat 64 (jLen K - 408 * i) :=
        (off_add _ _ _).symm
      have hP : PPost s s₂ [(sc (oHB K), 408)] := by
        refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
          (ws := [(sc (oHB K), jLen K - 408 * i), (sc (oHB K + (jLen K - 408 * i)), 408 - (jLen K - 408 * i))])
          (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
          (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · show Region.Sub ⟨pa s (sc (oHB K + (jLen K - 408 * i))), _⟩ ⟨pa s (sc (oHB K)), 408⟩
          rw [e]; exact Offset.sub_base _ (by omega_using [hf])
      refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      have k₁ := L₁.keepBytes hP₂.b hkp
      rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
      rw [hP₁.pa rbx_cs] at hb₂
      have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) (jLen K - 408 * i) (408 - (jLen K - 408 * i))
      rw [Nat.add_sub_cancel' (by omega_using [hf]), ← e, hb₂, k₁] at sp
      rw [sp, slice_of dc.c (show 408 * i - 32 + (jLen K - 408 * i) ≤ K.L.ctLen by omega_using [hi, hl, hcl, h0]), hbE,
        ite_eq_right (show ¬408 * i + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hf]), zc_drop K.L σ h32, hzl,
        List.take_of_length_le (by rw [List.length_drop, dcC, bytesAt_length]; omega_using [hcl])]

/-- While the seeds of fragment `i` are written. -/
structure SJ (W : DcWfB K.L oCT16) (σ : State) (i J : Nat) (s : State) : Prop where
  fi : FJ W σ i s
  sd : SeedsIs (Enc.rhoE K.L (dcEk K.L σ)) K.L.k (3 * i) J s
  hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f)

theorem seedJ_ok (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {J : Nat} (hJ : J < 4) {s : State}
    (h : SJ F.toDcWfB σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SJ F.toDcWfB σ i (J + 1)) := by
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd J hJ
  have L₀ := (dcXG F.toDcWfB σ).lay h.fi.eb.i.out
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := F.nbK
  refine WP.mono (seed_step L₀ (dcB_bases K.L) (by omega_using [hi, hJ, h16, this]) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocksJ_eq (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f)) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (K.oW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (zcE K.L σ) (3 * i + j) (BitVec.ofNat 8 0x1f) := by
  have hE : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  have hl := F.last
  have hn := F.nbJ
  rw [← hbE_blk hj (by rw [hE]; omega_using [hi, hl]), ← hb, bytesAt_slice _ _ (by omega_using [hj])]
  show bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
    bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW + Sample4.oHB) + BitVec.ofNat 64 (136 * j)) 136
  rw [off_add, off_add, Nat.add_assoc]

theorem fragJ_ok (F : DjFWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} {i : Nat} (hi : i < nb K.L)
    {s : State} (h : FJ F.toDcWfB σ i s) : WP isa (frag K b i) s (FJ F.toDcWfB σ (i + 1)) := by
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.jb i hi
  simp only [jbChk, Bool.and_eq_true] at hc
  unfold frag
  refine WP.seq (WP.mono (jblk_ok F hi h) fun s₁ ⟨hP₁, h15₁, hb₁⟩ => ?_)
  have f₁ := h.keep hP₁ h15₁ hc.2
  have i₁ : SJ F.toDcWfB σ i 0 s₁ := ⟨f₁, ⟨f₁.eb.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_bases]; exact hb₁⟩
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 0) (by decide) i₁) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 1) (by decide) i₂) fun s₃ i₃ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 2) (by decide) i₃) fun s₄ i₄ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 3) (by decide) i₄) fun s₅ i₅ => ?_)
  have L₅ := (dcXG F.toDcWfB σ).lay i₅.fi.eb.i.out
  refine WP.mono (sampleHAt16_ok hb (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have hk := hsm.2
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨⟨hE, hS⟩, hA⟩ := hk
  have hl := F.last
  have hn := F.nbJ
  have hpart : Partial (zcE K.L σ) := by rw [Partial, zcE_length]; exact F.part
  have hlen : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  refine ⟨⟨i₅.fi.eb.i.keep h₆.b hE, by rw [L₅.keepBytes h₆.b hS]; exact i₅.fi.eb.sb, ?_⟩, ?_⟩
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    refine EkF16.MatB16.three i₅.fi.eb.m L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega_using [hk]))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega_using [ht])]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS K)) = pa s₅ (sc (K.oW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocksJ_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    exact habs_blk hpart (by rw [hlen]; omega_using [hi, hl])

theorem fragsJ_ok (F : DjFWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} {s : State}
    (h : FJ F.toDcWfB σ 0 s) : WP isa (seqR (frag K b) 0 (nb K.L)) s (FJ F.toDcWfB σ (nb K.L)) := by
  have := seqR_ok (I := FJ F.toDcWfB σ) (nb K.L) 0 (fun k _ hk s hs => fragJ_ok F hb (by omega_using [hk]) hs) s h
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64.DjF16

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, with 16-bit polynomials

`kemDecapsJ16_correct`: the prologue and `m'` (`Dc16Dec.lean`);
`G(m' ‖ h)` alone, which gives the re-encryption's inputs in the context
before `K̄` (`hashG_ok`, `dcXG`); `ρ` to `SB` and `J`'s sponge zeroed; the
fragments (`fragsJ_ok`, `DjFrag16.lean`); `J(z ‖ c)` to `KB`, which moves
the inputs to the context of the re-encryption after the hashes (`dcX`,
`kbJ_ok`); the remaining entries of `Â` (`entsJ_ok`); and, if every
`SampleNTT` succeeded, the rest of the re-encryption and the choice of the
key.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DCK DM dcDk dcC dcEk dcM' dcG dcKb dcR dcW dcB dcB_bases dcChk dckChk DcWfB
  slice_of dcX)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (jLen hashG frag matJ)
open VG.Impl.MlKem.X86_64.Top16 (aP)

variable (K : Kem16)

/-- What decapsulation hashing `z ‖ c` in the fragments needs of the layout, besides the fragments'. -/
structure DjHWf : Prop extends DjFWf K where
  /-- The entries after the fragments are sampled four at a time. -/
  eS : 3 * nb K.L % 4 = 0 ∨ 4 * (K.L.k * K.L.k / 4) ≤ 3 * nb K.L
  noS : K.L.k * K.L.k ≤ 4 * (K.L.k * K.L.k / 4) ∨ K.L.k * K.L.k ≤ 3 * nb K.L
  -- `J(z ‖ c)` to `KB`
  kC : (copyChk (dcB K.L) (dcW K.L) (sc oKB) (sc (oHS K)) 32 && fkeep K [(sc oKB, 32)] (3 * nb K.L)) = true

variable {K}

/-- After `G(m' ‖ h)`: the re-encryption's inputs in the context before `K̄`, and `r15 = 1`. -/
abbrev GI (W : DcWfB K.L oCT16) (σ s : State) : Prop :=
  Enc.EIn K.L (dcXG W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s ∧ s.gpr .r15 = 1

/-- The re-encryption's inputs in its context, with the first `e` entries of `Â`. -/
abbrev EBX (W : DcWfB K.L oCT16) (σ : State) (e : Nat) (s : State) : Prop :=
  Enc16.EB16 K (dcX W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 e s

theorem hashG_ok (W : DcWfB K.L oCT16) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DM K.L σ s) :
    WP isa (hashG K) s (GI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * K.L.k + 96 = K.L.dkLen := rfl
  unfold hashG
  refine WP.mono (hash_ok (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * K.L.k + 32 + 32 ≤ K.L.dkLen by omega_using [hdk]), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  have hK : bytesAt s₁.mem (pa s₁ (sc oG)) 32 = (dcG K.L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₁]; rfl
  have hr : bytesAt s₁.mem (pa s₁ sigP) 32 = (dcG K.L σ).2 := by
    have e := bytesAt_drop s₁.mem (pa s₁ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₁.mem (pa s₁ (sc oG)) 64).drop 32 = bytesAt s₁.mem (pa s₁ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₁]; rfl
  refine ⟨⟨⟨hp, k₁, hK⟩, slice_of k₁.dk (show 384 * K.L.k + (384 * K.L.k + 32) ≤ K.L.dkLen by omega_using [hdk]), ?_, hr⟩, ?_⟩
  · rw [L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₁.cs .r15 (by decide), h.r15]

theorem rhoJ_ok (F : DjHWf K) {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) s (EBG F.toDcWfB σ 0) := by
  have L₀ := (dcXG F.toDcWfB σ).lay h.1.out
  have hrC := F.rC
  simp only [Bool.and_eq_true] at hrC
  refine WP.mono (copy_okL L₀ (show Reg.rbp ≠ .rdi by decide) hrC.1) fun s₁ ⟨hP₁, hb₁⟩ =>
    ⟨h.1.keep hP₁.b hrC.2, ?_, MatB16.zero _ _ _ (by rw [hP₁.cs .r15 (by decide), h.2])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.1.rho

theorem hzJ_ok (F : DjHWf K) {σ : State} {s : State} (h : EBG F.toDcWfB σ 0 s) :
    WP isa (.block (hzero K)) s (FJ F.toDcWfB σ 0) := by
  have L₁ := (dcXG F.toDcWfB σ).lay h.i.out
  have hzC := F.zC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hzC
  obtain ⟨hzin, ⟨hzE, hzS⟩, -⟩ := hzC
  exact WP.mono (EkF16.hzero16_ok L₁ hzin) fun s₂ ⟨hP₂, hz⟩ =>
    ⟨⟨h.i.keep hP₂.b hzE, by rw [L₁.keepBytes hP₂.b hzS]; exact h.sb,
      ⟨by rw [hP₂.cs .r15 (by decide)]; exact h.m.r15, fun _ he => absurd he (Nat.not_lt_zero _)⟩⟩,
      by rw [hP₂.pa rbx_cs, hz, HSponge.hstate_zero]⟩

/-- `J(z ‖ c)` to `KB`: the inputs move to the re-encryption's context. -/
theorem kbJ_ok (F : DjHWf K) {σ : State} {s : State} (h : FJ F.toDcWfB σ (nb K.L) s) :
    WP isa (copy (sc oKB) (sc (oHS K)) 32) s (EBX F.toDcWfB σ (3 * nb K.L)) := by
  have L₃ := (dcXG F.toDcWfB σ).lay h.eb.i.out
  have hkC := F.kC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hkC
  obtain ⟨hcp, ⟨hE, hS⟩, hA⟩ := hkC
  have hn := F.nbJ
  have hlen := zcE_length K.L σ
  have hjl : jLen K = 32 + K.L.ctLen := rfl
  refine WP.mono (copy_okL L₃ (show Reg.rbx ≠ .rdi by decide) hcp) fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have i₄ := h.eb.i.keep hP₄.b hE
  refine ⟨⟨⟨i₄.out.1, i₄.out.2.dc, i₄.out.2.k, ?_⟩, i₄.ek, i₄.m, i₄.r⟩,
    by rw [L₃.keepBytes hP₄.b hS]; exact h.eb.sb,
    ⟨by rw [hP₄.cs .r15 (by decide)]; exact h.eb.m.r15,
      fun e he f hf => L₃.keepPoly16 hP₄.b (hA e he) (h.eb.m.mat e he f hf)⟩⟩
  rw [hP₄.pa rbx_cs, hb₄, HSponge.bytesAt_stateAt, h.hs,
    ← HSponge.J_of_hstate (by rw [hlen]; omega_using [hn, hjl])]

theorem entsJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {σ : State} {s : State}
    (h : EBX F.toDcWfB σ (3 * nb K.L) s) :
    WP isa (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L)) s
      (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_ok (n, c) K.L.k K.oA (sc K.oW) (I := fun e s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' _ hs => absurd F.noS (by omega))
    (fun q hq _ hs => WP.mono (Enc16.quadE_step v (C := dcX F.toDcWfB σ) (by omega_using [h16, hq]) (F.enc.q q hq) hs.2) fun _ h => ⟨by omega, h.2⟩)
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega_using [this]) F.eS s ⟨Nat.le_refl _, h⟩
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact WP.mono this fun _ h => h.2

/-- `ρ` to `SB`, the fragments, `J(z ‖ c)` to `KB`, and the remaining entries of `Â`. -/
theorem matJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {b : Prog isa} (hb : BatchHOk16 b)
    {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (matJ K (n, c) b) s (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  unfold matJ
  exact WP.seq (WP.mono (rhoJ_ok F h) fun _ h₁ => WP.seq (WP.mono (hzJ_ok F h₁) fun _ h₂ =>
    WP.seq (WP.mono (fragsJ_ok F.toDjFWf hb h₂) fun _ h₃ => WP.seq (WP.mono (kbJ_ok F h₃) fun _ h₄ =>
      entsJ_ok v F h₄))))

/-- The rest of the re-encryption, if every `SampleNTT` succeeded. -/
theorem ifRestJ_ok (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {σ s : State}
    (h : EBX F.toDcWfB σ (K.L.k * K.L.k) s) :
    WP isa (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) s (Decaps16.EncO16 F.toDc16Wf σ) := by
  refine ifOk_ok (fun s₁ hP hne => Enc16.rest_ok hK v (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
    (Enc16.ER0.start (h.flag hP F.enc) (KeyGen.r15_ne h.m.r15 hne))) fun s₁ hP he => ?_
  have h₁ := h.flag hP F.enc
  exact ⟨h₁.i.out, h₁.m.r15, fun ho => absurd ho (KeyGen.r15_eq h.m.r15 he)⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true) (σ : State) (hp : (decapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemDecapsJ16 K v.callee (n, c) b) σ t s' ∧ abiPreserved σ s' ∧ (decapsK K.L).post σ s' := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok F.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (dec_ok hK F.toDc16Wf hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashG_ok F.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (matJ_ok hS F hB h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (ifRestJ_ok hK v F h₄) fun s₅ h₅ =>
            WP.seq (WP.mono (select_okD F.toDcWfB (EncO16.sel (W := F.toDc16Wf) h₅)) fun s₆ h₆ =>
              WP.mono (topEpi_ok h₆.dc.top (h₆.hin F.toDcWfB hp)) fun s₇ ⟨hr, hg, hm⟩ =>
                (⟨hg, post_of F.toDcWfB h₆ hr hm⟩ : gprPreserved σ s₇ ∧ (decapsK K.L).post σ s₇)))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, constant time

`kemDecapsJ16_ct`: two runs whose pointers and `ρ` agree leak the same. The
fragments' blocks of `pad(z ‖ c)` and the sponge's state, which only the
fourth Keccak state absorbs, are at fixed addresses (`jblk` and the copies
pass the taint analysis from the pointers, `DjTWf`), and the sampling's
branches and addresses depend on the seeds of `ρ` alone, as in
`kemEncaps16_ct`; the rest leaks only the pointers, as in the
decapsulation of `u32` polynomials.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DM dcEk dcR dcW dcB dcB_bases DcWfB R dc_lrel rho_pub dcXA)
open VG.Proof.MlKem.X86_64.EkF (relFalse)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (hashG jblk frag matJ)

variable (K : Kem16)

/-- The taint checks of the pieces the fused decapsulation adds, from the pointers. -/
structure DjTWf : Prop where
  rbpIn : inB (dcB K.L) (.rbp, 0) 1 = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (.block (hzero K)) h).isSome = true
  jT : ∀ i < nb K.L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (jblk K i) h).isSome = true
  kT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14])
    (copy (sc oKB) (sc (oHS K)) 32) h).isSome = true
  ij : ∀ i < nb K.L, ∀ J < 4, (3 * i + J) / K.L.k < 4 ∧ (3 * i + J) % K.L.k < 4

variable {K}

section
variable (F : DjHWf K) (T : DjTWf K)
include F T

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trLD {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) c h).isSome = true) :
    RelCT isa (LRel (dcR K.L) (dcW K.L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r14] (fun _ _ h =>
    fa4 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)
      (h.eq (p := (.r12, 0)) (l := 1) F.inBs.2.1) (h.eq (p := (.r14, 0)) (l := 1) F.inBs.2.2)) ht

theorem rhoJ_tr :
    RelCT isa (R K.L (GI F.toDcWfB)) (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := F.rhoT
  exact rel2_of (taintRel [.rbx, .rbp] (fun _ _ h =>
      fa2 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)) t)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel F.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc

theorem hzJ_tr : RelCT isa (R K.L fun σ s => EBG F.toDcWfB σ 0 s) (.block (hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc

theorem kbJ_tr : RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) (copy (sc oKB) (sc (oHS K)) 32)
    fun _ _ => True := by
  obtain ⟨_, t⟩ := T.kT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc

end

theorem hashG_tr (W : DcWfB K.L oCT16) : RelCT isa (R K.L (DM K.L)) (hashG K) fun _ _ => True := by
  unfold hashG
  exact rel2_of (hash_tr (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-- Before fragment `i`, for the `ρ` of `dk`'s key. -/
abbrev FJρ (W : DcWfB K.L oCT16) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (decapsK K.L).pre σ ∧ FJ W σ i s ∧ Enc.rhoE K.L (dcEk K.L σ) = ρ

theorem fragJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) {i : Nat} (hi : i < nb K.L) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ i s) (frag K b i) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.jT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.jb i hi
  simp only [jbChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧ FJρ F.toDcWfB ρ i x ∧
    FJρ F.toDcWfB ρ i y) (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FJρ F.toDcWfB ρ i x → WP isa (jblk K i) x fun x' =>
        PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (jblk_ok F.toDjFWf hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep hP h15 hc.2).eb.sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trLD F T t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ (dcR K.L) (dcW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (dcB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 0) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 1) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 2) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 3) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq F.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc,
      ⟨σ₁, p₁, h₁, rfl⟩, ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem fragsJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ 0 s) (seqR (frag K b) 0 (nb K.L))
      (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) := by
  have := seqR_tr (R := fun i => R K.L fun σ s => FJ F.toDcWfB σ i s) (nb K.L) 0 fun k _ hk =>
    relInv (fun σ s hp h => fragJ_ok F.toDjFWf hB (by omega_using [hk]) h) (fragJ_tr F T hB (by omega_using [hk]))
  rwa [Nat.zero_add] at this

theorem quadJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {q : Nat} (hq : q < K.L.k * K.L.k / 4) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (4 * q) s)
      (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) fun _ _ => True := by
  have hc := F.enc.q q hq
  simp only [Enc16.quadEChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hk4 := F.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (dcR K.L) (dcW K.L) ρ K.L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad16_tr (ρ := ρ) v (dcB_bases K.L) (by omega_using [hq, h16])
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this],
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this]⟩) hc.1.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s)
      (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L))
      (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_tr (n, c) K.L.k K.oA (sc K.oW)
    (R := fun e => R K.L fun σ s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega_using [he, he', h3]))
    (fun q hq => relInv (fun σ s hp hs => WP.mono (Enc16.quadE_step v (C := Decaps.dcX F.toDcWfB σ) (by omega_using [h16, hq]) (F.enc.q q hq) hs.2)
        fun _ h => ⟨by omega, h.2⟩)
      (RelCT.mono (quadJ_tr v F hq)
        (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h))
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega_using [this]) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) (T : DjTWf K) {b : Prog isa}
    (hB : BatchHOk16 b) :
    RelCT isa (R K.L (GI F.toDcWfB)) (matJ K (n, c) b) (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  unfold matJ
  exact RelCT.seq (relInv (I' := fun σ s => EBG F.toDcWfB σ 0 s) (fun σ s hp h => rhoJ_ok F h) (rhoJ_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FJ F.toDcWfB σ 0 s) (fun σ s hp h => hzJ_ok F h) (hzJ_tr F T))
      (RelCT.seq (fragsJ_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s) (fun σ s hp h => kbJ_ok F h)
          (kbJ_tr F T)) (entsJ_tr v F))))

/-- The rest of the re-encryption if every `SampleNTT` succeeded. -/
theorem ifRestJ_tr (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s)
      (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) x ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
      (RelCT.mono (Enc16.rest_tr hK v (C := dcXA F.toDcWfB) (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
        (ρ := ρ)) ?_
        fun _ _ _ => trivial) fun _ _ _ => trivial
    rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk K.L.k (Enc.rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post (dcXA F.toDcWfB).bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc16.ER0.start (h₁.flag hx F.enc) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, Enc16.ER0.start (h₂.flag hy F.enc) o₂⟩⟩
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
      ⟨_, _, _, rfl, Decaps.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Decaps.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) (T : DjTWf K)
    {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b) :
    ConstantTime isa (decapsK K.L).pre (decapsK K.L).pub (kemDecapsJ16 K v.callee (n, c) b) := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecapsJ16
  refine RelCT.seq (relInv (I' := fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok F.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM K.L) (fun σ s hp hs => dec_ok hK F.toDc16Wf hp hs.1 hs.2)
    (dec_tr hK F.toDc16Wf)) ?_
  refine RelCT.seq (relInv (I' := GI F.toDcWfB) (fun σ s hp hs => hashG_ok F.toDcWfB hp hs)
    (hashG_tr F.toDcWfB)) ?_
  refine RelCT.seq (matJ_tr hS F T hB) ?_
  refine RelCT.seq (relInv (I' := EncO16 F.toDc16Wf) (fun σ s _ hs => ifRestJ_ok hK v F hs) (ifRestJ_tr hK v F)) ?_
  refine RelCT.seq (relInv (I' := DEnd K.L) (fun σ s _ hs => select_okD F.toDcWfB hs.sel)
    (RelCT.mono (select_tr F.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩) fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkSel16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: encapsulation hashing the key, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the encapsulation with
16-bit polynomials (`kemEncaps16`); any other, the one with polynomials of
`u32`s (`kemEncaps`). As `Sel16.lean`, with `ek16_ctl` and `ek16_sp` for
the control flow and the stack pointer of `kemEncaps16`, which is proven
for the layout with only the first `n` bytes of `scratch` and leaves the
rest of it as it was (`encapsSel_keep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `ctlOk` of code that calls the 16-bit sampler `c` of the implementation
`v` (`S : S16Ok c`) and the K-PKE functions (`hK`), and inlines the fragment
`b` (`B : BatchHOk16 b`). -/
tactic_template "ek16_ctl " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).ctl | (closed_in $b; s16_ctl $v $c $S $hK; done)
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite) | rfl))

/-- That code that calls the 16-bit sampler `c` of the implementation `v` and
the K-PKE functions, and inlines the fragment `b`, never writes the stack pointer. -/
tactic_template "ek16_sp " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).sp | (closed_in $b; s16_sp $v $c $S $hK; done)
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite) | rfl))

/-- Encapsulation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem xdLe_batch {k : Nat} {b : Prog isa} (B : BatchHOk16 b) : xdLe k b = true :=
  xdLe_of_le (by rw [B.xd]; exact Nat.zero_le _)

/-- That the calls of code that calls the 16-bit sampler `c` of the
implementation `v` and the K-PKE functions, and inlines the fragment `b`, use
at most `k` bytes of stack (a goal `xdLe k _ = true`). -/
tactic_template "ek16_xd " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible apply xdLe_batch $B | (closed_in $b; s16_xd $v $c $S $hK; done)
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite) | rfl))

theorem encaps16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsat : ∃ s, (encK K.L).pre s) :
    Verified X86_64.target (kemEncaps16 K v.callee (m, c) b) (encK (narrowL K.L n)) :=
  Verified.of_correct (kemEncaps16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemEncaps16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, encK_pre hn hs⟩))

theorem encapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) (W : Ek.EkWf K.L)
    {wc wd : List Nat} (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (encK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemEncaps16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemEncaps K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsSel K v.callee) k := by
  unfold kemEncapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (encK_widen hn (encaps16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemEncaps_correct v W C hctl) (kemEncaps_ct v W C) hk

/-- Encapsulation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem encapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemEncaps16 K v.callee (m, c) b))
    (hd : (kemEncaps16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (encK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemEncapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .r8 + BitVec.ofNat 64 i) = s.mem (s.gpr .r8 + BitVec.ofNat 64 i) := by
  unfold kemEncapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, -, -, -, d8, d9, -, -, -, -, -, -, -, -, -, b5, -, -, -, -, o5⟩ := id hp
  refine verified_keepTail (encaps16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (encK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o5 (fun r hr => ?_) b5 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d8
  · exact .inr d9
  · exact .inl rfl

/-- No instruction of `kemEncapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem encapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemEncaps16 K v.callee (n, c) b).all p = true)
    (h : (kemEncaps K.L v.callee).all p = true) : (kemEncapsSel K v.callee).all p = true := by
  unfold kemEncapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkTop`, which the modules that import this one used -/

section

/-!
# ML-KEM on x86-64: encapsulation hashing the key

`kemEncaps L v.callee` for any implementation `v` of `vg_mlkem_sample_ntt4`,
with the sponge functions (`EkScalar.lean`), and a state its contract
permits (`encapsSat`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- A state satisfying the precondition of `vg_mlkem*_encaps` for keys of
`ekLen` bytes, ciphertexts of `ctLen` bytes and `scr` bytes of working space. -/
def encapsSat (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000
    | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, ctLen⟩, ⟨0x10000, scr⟩]

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the decapsulation with
16-bit polynomials that hashes `z ‖ c` in the fragments (`kemDecapsJ16`);
any other, the one with polynomials of `u32`s (`kemDecaps`). As
`EkSel16.lean`, whose `ek16_ctl` and `ek16_sp` give its control flow and
stack pointer.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Decapsulation hashing `z ‖ c` in the fragments, against the contract of
`K` with the first `n` bytes of `scratch`. -/
theorem decapsJ16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsat : ∃ s, (decapsK K.L).pre s) :
    Verified X86_64.target (kemDecapsJ16 K v.callee (m, c) b) (decapsK (narrowL K.L n)) :=
  Verified.of_correct (kemDecapsJ16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemDecapsJ16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, decapsK_pre hn hs⟩))

theorem decapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) (W : Decaps.DcWf K.L) {wc wd : List Nat}
    (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (decapsK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemDecaps K.L v.callee) = true) :
    Verified X86_64.target (kemDecapsSel K v.callee) k := by
  unfold kemDecapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (decapsK_widen hn (decapsJ16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemDecaps_correct v W C hctl) (kemDecaps_ct v W C) hk

/-- Decapsulation hashing `z ‖ c` in the fragments leaves `scratch` from its
`n`-th byte on as it was. -/
theorem decapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemDecapsJ16 K v.callee (m, c) b))
    (hd : (kemDecapsJ16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (decapsK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemDecapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .rcx + BitVec.ofNat 64 i) = s.mem (s.gpr .rcx + BitVec.ofNat 64 i) := by
  unfold kemDecapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, d5, -, -, -, -, -, -, -, b4, -, -, -, o4⟩ := id hp
  refine verified_keepTail (decapsJ16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (decapsK_pre hn hp)
    (by rw [hwr]; exact prefix2 hn) he o4 (fun r hr => ?_) b4 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr d5
  · exact .inl rfl

/-- No instruction of `kemDecapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem decapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemDecapsJ16 K v.callee (n, c) b).all p = true)
    (h : (kemDecaps K.L v.callee).all p = true) : (kemDecapsSel K v.callee).all p = true := by
  unfold kemDecapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64
