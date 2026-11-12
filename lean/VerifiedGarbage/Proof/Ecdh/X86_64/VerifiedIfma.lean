module

public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.P256.X86_64.WinJac
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdh.X86_64.LitIfma
public import VerifiedGarbage.Proof.Ecdh.X86_64.Contract
public import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
public import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.P256.X86_64.WinJac
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdh.X86_64.LitIfma
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Contract
meta import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
meta import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Ecdh.X86_64.Verified

import VerifiedGarbage.Proof.Ecdh.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.EcdhLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MxcsrInline

/-!
# ECDH over P-256 on x86-64 with AVX512_IFMA: `Verified`

As `VerifiedAdx.lean`, for the code whose window method's loop is in vectors
(`Impl/P256/X86_64/Ifma/Ecdh.lean`): `mulQP256Ifma_ok` is `mulQJO_with`
(`WinJacOdd.lean`) with `vwindowO_ok` (`Proof/P256/X86_64/Ifma/EcdhLoop.lean`)
for its window method, which also writes the vectors' part of the working
space (`eV`), apart from what the exchange keeps (`mulQP256Ifma_w`). The code
loads MXCSR, and loads the caller's back (`exchangeP256Ifma_ctl`), so the
calling convention's obligations are `ecdh_x86_of_ctl`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64

/-- The window method's working space for P-256 leaves the vectors' part (`EVLay`). -/
theorem evLay (hI : Weierstrass.X86_64.InvSounds) :
    Proof.P256.X86_64.Ifma.EVLay (Impl.Ecdh.X86_64.Cfg.jwinCfgO p256x) size where
  lay := jwLayQO (p256x_ok hI) (Or.inl rfl)
  n4 := rfl
  sz := by decide
  below := by decide
  ro := by decide
  bits := by decide
  mo := by decide
  T := by decide

/-- The window method's selection of an entry does not write `r12`, where MXCSR is saved. -/
theorem digitSel_r12 : ((Impl.Ecdh.X86_64.Cfg.jwinCfgO p256x).digitO ++
    (Impl.Ecdh.X86_64.Cfg.jwinCfgO p256x).select).all (fun i => !Taint.clobbers i .r12) = true := by
  decide +kernel

theorem negY_r12 : (Impl.Ecdh.X86_64.Cfg.jwinCfgO p256x).tc.negY.all (fun i => !Taint.clobbers i .r12) = true := by
  decide +kernel

theorem noR12_of_all {l : List Instr} (h : l.all (fun i => !Taint.clobbers i .r12) = true) :
    ∀ i ∈ instrs (Code.block (C := Cond) l), Taint.clobbers i .r12 = false := fun i hi => by
  have := List.all_eq_true.mp h i hi
  simpa using this

/-- The window method with its loop in vectors computes `[d]P` on P-256 (`mulQJO_with`,
`vwindowO_ok`), writing the vectors' part of the working space too. -/
theorem mulQP256Ifma_ok (hI : Weierstrass.X86_64.InvSounds) (hL : Weierstrass.Law Spec.P256.curve)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) (hK : Weierstrass.KilledByN Spec.P256.curve) :
    MulOk p256x mulQP256Ifma (mulQJW p256x ++ Proof.P256.X86_64.Ifma.eV) :=
  mulQJO_with (p256x_ok hI) (Or.inl rfl) hL hK (by decide) (by decide)
    (fun w hw => Or.inr (by rw [List.mem_singleton.mp hw]; decide))
    (fun j hj t ht w hw => by
      rw [List.mem_singleton.mp hw]
      have ht' : t < 256 := ht
      have h2 : bitsAt p256x.n 2 + 256 ≤ 5472 := by decide
      have hm : bitsAt p256x.n j ≤ bitsAt p256x.n 2 := by
        unfold bitsAt; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      exact Or.inl (by show bitsAt p256x.n j + t + 1 ≤ 5472; omega))
    (fun hP _ hkJ _ _ hs hM hF => Proof.P256.X86_64.Ifma.vwindowO_ok (evLay hI)
      (Weierstrass.unitMod_pow_two (p256x_ok hI).p_odd _) hL (p256x_ok hI).am3 hO (p256x_ok hI).p_lt
      (show p256x.mont 1 < p256x.C.p from Nat.mod_lt _ (by decide))
      (show Weierstrass.toM p256x.C.p (2 ^ (64 * p256x.n)) (p256x.mont 1) = 1 by
        rw [toM_cmont (p256x_ok hI)]; rfl)
      (by decide) (by decide) (by decide) (noR12_of_all digitSel_r12) (noR12_of_all negY_r12) hP hkJ hs hM hF)

/-- What the multiplication writes keeps the constants, `d` and the flag (`MulW`). -/
theorem mulQP256Ifma_w (hI : Weierstrass.X86_64.InvSounds) :
    MulW p256x (mulQJW p256x ++ Proof.P256.X86_64.Ifma.eV) where
  fixed := (mulQJ_w (p256x_ok hI)).fixed.append fun w hw =>
    Or.inr (by rw [List.mem_singleton.mp hw]; decide)
  d := apart_append (mulQJ_w (p256x_ok hI)).d fun w hw =>
    Or.inl (by rw [List.mem_singleton.mp hw]; decide)
  flag := apart_append (mulQJ_w (p256x_ok hI)).flag fun w hw =>
    Or.inl (by rw [List.mem_singleton.mp hw]; decide)

theorem exchangeP256Ifma_ctl : ctlOk exchangeP256Ifma = true := by lit_decide

theorem ecdh_x86_ifma (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) (hK : Weierstrass.KilledByN Spec.P256.curve) (s : State)
    (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP256Ifma.inline s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  ecdh_x86_of_ctl (p256x_ok hI) hL (mulQP256Ifma_ok hI hL hO hK) (mulQP256Ifma_w hI)
    (fun _ h => { pre_of h with }) (fun _ _ => post_of) rfl (by lit_decide) (by lit_decide)
    exchangeP256Ifma_ctl s hs

/-- `exchangeP256Ifma` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def exchangeP256IfmaErased : Prog isa := Code.erase exchangeP256Ifma

materialize_shared exchangeP256IfmaErased

theorem ecdh_ct_ifma : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256Ifma :=
  VG.Taint.constantTime_mapBlocks (c' := exchangeP256IfmaErased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h0)
    rfl (by taint_decide)

/-! ## The contract with 16 bytes of stack

The code uses 8, for its calls' return address; clearing the vector registers at the level `evex`
(`X86_64.Scrub.withScrubAll`) needs 16. -/

/-- A contract with stack asks more than the same with none. -/
theorem pre_stack0_of {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    {n : Nat} {s : State} (h : (sig.contract abi pre post wa n leak).pre s) :
    (sig.contract abi pre post wa 0 leak).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨hw, hrd, hwr, hpw, hres, hb, hp⟩ := h
    have hsub : ∀ r ∈ abi.reserved 0 s, r ∈ abi.reserved n s := by
      intro r hr
      simp only [abi, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      exact List.mem_cons.mpr (.inl hr)
    refine ⟨?_, hrd, hwr, hpw, fun r hr => hres r (hsub r hr), hb, hp⟩
    simp only [abi] at hw ⊢
    split at hw
    · rename_i hl; simp only [hl, ite_true]
    · rename_i hl; simp only [hl, ite_false]; exact ⟨trivial, hw.2⟩

/-- The calls' return address is within 16 bytes of stack. -/
theorem hole_sub16 (sp : Addr) : Region.Sub (hole sp) ⟨sp - 16, 16⟩ := fun a ha => by
  simp only [hole, Region.Contains] at ha ⊢
  bv_omega

/-- No buffer is on the calls' return address, for a contract with 16 bytes of stack. -/
theorem clear_of_pre16 {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract abi pre post wa 16 leak).pre s) : Clear (hole (s.gpr .rsp)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨_, hrd, hwr, _, hres, _⟩ := h
    intro r hr
    have hh : (⟨s.gpr .rsp - 16, 16⟩ : Region) ∈ abi.reserved 16 s := by
      simp [abi, stackBelow]
    rcases List.mem_append.mp hr with hr | hr
    · rw [show s.rd = abi.rd s from rfl, hrd] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm.sub_right (hole_sub16 _)
    · rw [show s.wr = abi.wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm.sub_right (hole_sub16 _)

theorem implies16 :
    ecdhX86_64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi 16) :=
  ⟨fun s hs => implies.pre s (pre_stack0_of hs), fun s s' hs hp => implies.post s s' (pre_stack0_of hs) hp,
    fun s₁ s₂ h₁ h₂ hp => implies.pub s₁ s₂ (pre_stack0_of h₁) (pre_stack0_of h₂) hp, by
      sig_implies_sat [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
        Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, X86_64.abi,
        X86_64.argRegs, satState] [satState] using satState⟩

/-- The output is apart from the calls' return address. -/
theorem ecdh_patch16 (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi 16).pre s)
    (hp : ecdhX86_64.post s b) : ecdhX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies16.pre s hs
  have hb := Clear.wr_bytes (clear_of_pre16 hs) (p := s.gpr .rdi) (n := 32)
    (by rw [hwr]; simp) (by decide)
  simpa only [ecdhX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem ecdh_verified_ifma (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) (hK : Weierstrass.KilledByN Spec.P256.curve) :
    Verified X86_64.target exchangeP256Ifma
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi 16) :=
  Verified.of_inline_ct (by lit_decide) (ecdh_x86_ifma hL hI hO hK) ecdh_ct_ifma implies16
    (fun _ h => clear_of_pre16 h) ecdh_patch16

end VG.Proof.Ecdh.X86_64
