module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract
meta import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn

/-!
# Montgomery arithmetic modulo the curves' `p` and `n`, as functions, on PPC64LE: verified

Each modulus of `Impl.Weierstrass.Mont.moduli` is one the functions support
(`ModOk`), so each of its functions meets the contract of its `Api`: the
proof against `mulPPC`, `addPPC` or `subPPC`, which it implies, constant
time by taint tracking (only the pointer and the offsets, in `r3`–`r6`, are
public), and a state satisfying it (`sat`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont Impl.Weierstrass.Mont

/-- The zero-extension, then code that is constant time for states agreeing
on `r3`–`r6`: constant time for states agreeing on `r3` and the offsets' low
halves. -/
theorem ct_zext {Pre : State → Prop} {c : Prog isa}
    (h : ConstantTime isa (fun _ => True) (VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6])) c) :
    ConstantTime isa Pre ppcPub (.seq (.block zext) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
  simp only [ofs32] at h4 h5 h6
  cases e₁ with
  | seq z₁ c₁ =>
    cases e₂ with
    | seq z₂ c₂ =>
      obtain ⟨rfl, rfl⟩ := exec_zext z₁
      obtain ⟨rfl, rfl⟩ := exec_zext z₂
      have ag : VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) (zextState s₁) (zextState s₂) := by
        refine ⟨hsp, fun r hr => ?_⟩
        simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          simp only [zextState, lo, VG.Proof.Mont.PPC64LE.write_gpr, reduceCtorEq, ite_false, ite_true, h3, h4,
            h5, h6]
      rw [h _ _ _ _ _ _ trivial trivial ag c₁ c₂]

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

theorem numAt_zero (ws : Addr) (o : BitVec 32) (k : Nat) : numAt (fun _ => 0) ws o k = 0 :=
  read_zero _ _

/-- A state satisfying the preconditions: `ws` at `0x1000`, the numbers at
offset 0, all zero. -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem fit_zero (M : Modulus) (hk : M.k ≤ 9) : M.Fit 0 0 0 := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fits, ownAt, ownBytes, h0] <;> omega

/-- `mul` meets its contract for any modulus the functions support, given its constant time. -/
theorem mul_verified (M : Modulus) (hM : ModOk M.k M.m)
    (hct : ConstantTime isa (mulPPC M).pre (mulPPC M).pub (mulFn M.k M.m)) :
    Verified PPC64LE.target (mulFn M.k M.m) (M.mulContract PPC64LE.abi) :=
  Verified.of_correct (mul_ppc hM) hct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      sat := ⟨sat, by
        sig_reduce [Sig.wfPre, sig, PPC64LE.abi, PPC64LE.argRegs, sat]
        refine ⟨trivial, rfl, rfl, by simp, by simp, by simp, ?_, ?_⟩
        · exact fit_zero M hM.n9
        · rw [numAt_zero]; exact hM.m0⟩ }

/-- `add` meets its contract for any modulus the functions support, given its constant time. -/
theorem add_verified (M : Modulus) (hM : ModOk M.k M.m)
    (hct : ConstantTime isa (addPPC M).pre (addPPC M).pub (addFn M.k M.m)) :
    Verified PPC64LE.target (addFn M.k M.m) (M.addContract PPC64LE.abi) :=
  Verified.of_correct (add_ppc hM) hct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      sat := ⟨sat, by
        sig_reduce [Sig.wfPre, sig, PPC64LE.abi, PPC64LE.argRegs, sat]
        refine ⟨trivial, rfl, rfl, by simp, by simp, by simp, ?_, ?_⟩
        · exact fit_zero M hM.n9
        · rw [numAt_zero]; have := hM.m0; omega⟩ }

/-- `sub` meets its contract for any modulus the functions support, given its constant time. -/
theorem sub_verified (M : Modulus) (hM : ModOk M.k M.m)
    (hct : ConstantTime isa (subPPC M).pre (subPPC M).pub (subFn M.k M.m)) :
    Verified PPC64LE.target (subFn M.k M.m) (M.subContract PPC64LE.abi) :=
  Verified.of_correct (sub_ppc hM) hct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subPPC, ppcPre, ppcPub, ofs32, PPC64LE.abi,
        PPC64LE.argRegs]
      sat := ⟨sat, by
        sig_reduce [Sig.wfPre, sig, PPC64LE.abi, PPC64LE.argRegs, sat]
        refine ⟨trivial, rfl, rfl, by simp, by simp, by simp, ?_, ?_⟩
        · exact fit_zero M hM.n9
        · rw [numAt_zero]; exact ⟨hM.m0, hM.m0⟩⟩ }

end VG.Proof.Weierstrass.PPC64LE.Mont
