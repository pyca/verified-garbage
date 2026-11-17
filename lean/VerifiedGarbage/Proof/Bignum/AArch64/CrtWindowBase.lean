module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
import VerifiedGarbage.Proof.Framework.ModArith
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCodeCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.AArch64.CrtWindowVerified`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtImplies`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on AArch64: the shared contract

`crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`) states the shared contract of
`vg_rsa_private_crt` on the registers and the stack (`crt_implies`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64
open VG.Proof.Rsa.AArch64 (crtA crtPA KeyProduct privateCrtProductContract stackArgs_ten)

/-- A state meeting `crtA.pre`: a 64-byte modulus and input, one-byte
primes, exponents and `qInv`, and the stack arguments at `0x10000`. -/
def crtSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 64
    | .x6 => 0x4000 | .x7 => 1 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10048 then 0x20
    else if a = 0x10001 then 0x41 else if a = 0x10008 then 1 else if a = 0x10011 then 0x42
    else if a = 0x10018 then 1 else if a = 0x10021 then 0x43 else if a = 0x10028 then 1
    else if a = 0x10031 then 0x44 else if a = 0x10038 then 1 else if a = 0x10042 then 0x02
    else if a = 0x10049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem crtSat_pre : (Proof.Rsa.privateCrtContract abi 0).pre crtSatState := by
  sig_sat_check [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
    List.append_eq]

theorem crt_implies : crtA.Implies (Proof.Rsa.privateCrtContract abi 0) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA,
      stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by simp only [stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := ⟨_, crtSat_pre⟩

/-- The key of `crtSatState` is zeros, whose product is the modulus. -/
theorem crtSat_product : KeyProduct crtSatState := by
  unfold KeyProduct
  decide

theorem crtP_implies : crtPA.Implies privateCrtProductContract where
  pre := fun s ⟨h, hk⟩ => ⟨crt_implies.pre s h, hk⟩
  post := fun s s' ⟨h, _⟩ hp => crt_implies.post s s' h hp
  pub := fun s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ hp => crt_implies.pub s₁ s₂ h₁ h₂ hp
  sat := ⟨_, crtSat_pre, crtSat_product⟩

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtWindowCode`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on AArch64: correctness

`code`, from a state its contract allows, writes `privateCrt` of its inputs
(`crtCode_correct`), against `crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA)

/-- `vg_rsa_private_crt` with Montgomery multiplication `M` and the key
checks `C`, for a key with `G n p q`. -/
theorem crtCodeWith_correct (W : Window) (M : Mont) (S : Selector) {C : List (Prog isa)}
    {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G) (s : State) (h : crtA.pre s)
    (hG : G (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))) :
    ∃ t s', Exec isa (VG.Impl.Rsa.AArch64.WindowFive.codeWith C W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      crtA.post s s' := by
  have c := crtCtx_of h
  clear h
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (VG.Impl.Rsa.AArch64.WindowFive.codeWith C W.code S.code M.mm) s fun s' => abiPreserved s s' ∧ crtA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold VG.Impl.Rsa.AArch64.WindowFive.codeWith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (h₁.keep.gpr .x2 (by decide))
    (by rw [h₁.keep.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
    (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (s.gpr .x3).toNat) (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false := by simpa using hb
    exact WP.mono (crtFail_ok hpre)
      fun t hp => crtCode_fin h₁ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true := by simpa using hb
    exact WP.mono (dispatch_ok W M S hpre hv hC hG) fun t ⟨Mk, hp, hiff⟩ => crtCode_fin h₁ k₂ hp
      (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`. -/
theorem crtCode_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : crtA.pre s) :
    ∃ t s', Exec isa (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      crtA.post s s' :=
  crtCodeWith_correct W M S checks_okG s h trivial

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Wider-window RSA CRT against the unchanged shared contract, and
`vg_rsa_private_crt_precomputed`, its code without the check `p q = n`,
against `privateCrtProductContract`, for keys that have it. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm)
      (Proof.Rsa.privateCrtContract abi 0) :=
  Verified.of_correct (crtCode_correct W M S) (crtCode_constantTime_of W M S) crt_implies

theorem verifiedGiven (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.codeGiven W.code S.code M.mm)
      Proof.Rsa.AArch64.privateCrtProductContract :=
  Verified.of_correct (k := Proof.Rsa.AArch64.crtPA)
    (fun s (h : Proof.Rsa.AArch64.crtPA.pre s) => crtCodeWith_correct W M S checksGiven_okG s h.1 h.2)
    (crtCodeWith_constantTime W M S checksGiven_ct checksGiven_okG) crtP_implies

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.WindowSharedInterface`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64.WindowFive

theorem window_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64}
    {X Xc x E v : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2^30) (hR : Nat.Coprime (2^(64*w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x^E * 2^(64*w) % X)
    (hv : v < 32) (hn : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa code s (WindowPost s P w mi X Xc Q x E v) := by
  have raw : CrtWindowFive.CTab s.mem P w X False 0 := ⟨ht.tab,ht.lt,False.elim⟩
  refine WP.mono (guarded_ok hc raw hw hw' hy hv hn) fun t ⟨ct,yt,vt,nt,bt,ft,kt⟩ => ?_
  have fw := ft.mono (rawWindowRanges_sub w)
  refine ⟨ct,ht.of_win fw hc.scrT.nowrap,yt,?_,ft,kt,nt,bt,?_⟩
  · intro hQ
    have he : wv s.mem P (slot w aY) w % X = x^E * 2^(64*w) % X := hyv hQ
    have ht' : wv s.mem P (slot w (8+v)) w % X = x^v * 2^(64*w) % X := ht.val hQ v hv
    have hm : wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X =
        (x^E * 2^(64*w))^32 * (x^v * 2^(64*w)) % X := by
      rw [Nat.mul_mod, Nat.pow_mod, he, ht', ← Nat.pow_mod, ← Nat.mul_mod]
    have hr : (x^E * 2^(64*w))^32 * (x^v * 2^(64*w)) =
        (x^(32*E+v) * 2^(64*w)) * (2^(64*w))^32 := by
      rw [Nat.mul_pow,Nat.pow_add,← Nat.pow_mul, Nat.mul_comm E 32]
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [hr] at hm
    exact ModArith.mod_eq_of_mul_mod_eq (hR.pow_left 32)
      ((show wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w^32 * wv s.mem P (slot w (8+v)) w % X from vt).trans hm)
  · intro k hk he hj hn' hb
    apply ft.word_eq _ (by have := hdr_lt_slot w 8 hk; have := hc.scrT.nowrap; omega_using [hk])
    intro r hr
    simp only [rawWindowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (have := hdr_lt_slot w aAcc hk; simp only; omega)
      | (have := hdr_lt_slot w aTmp hk; simp only; omega)
      | (have := hdr_lt_slot w aY hk; simp only; omega)
      | (have := hdr_lt_slot w Crt.aT hk; simp only; omega_using [this])
      | (simp only; omega)

def window : Window := ⟨code,window_ok,code_ct⟩

end VG.Proof.Bignum.AArch64.WindowShared

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

def body : Window := WindowShared.window

theorem body_keeps_link : ∀ i ∈ instrs body.code, vdstOf i ≠ some .v7 := by
  have hb : body.code.allInstrs (fun i => vdstOf i != some .v7) = true := by decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at hb
  intro i hi
  exact bne_iff_ne.mp (hb i hi)

def called : Window := WindowCall.outlined body "vg_rsa_square_window5" body_keeps_link

def code : Prog isa :=
  VG.Impl.Rsa.AArch64.WindowFive.code called.code WindowVector.selector.code Mont.calledProductEight.mm

theorem base_verified : Verified target code (Proof.Rsa.privateCrtContract abi 0) :=
  verified called Mont.calledProductEight WindowVector.selector

/-- `vg_rsa_private_crt_precomputed`: `code` without the check `p q = n`. -/
def codeGiven : Prog isa :=
  VG.Impl.Rsa.AArch64.WindowFive.codeGiven called.code WindowVector.selector.code Mont.calledProductEight.mm

theorem given_verified : Verified target codeGiven Proof.Rsa.AArch64.privateCrtProductContract :=
  verifiedGiven called Mont.calledProductEight WindowVector.selector

end VG.Proof.Bignum.AArch64.WindowFive
