module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.CallEntry
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MillerRabin.X86.CallPre
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.MillerRabin.X86.CallSetup
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `MillerRabin.X86.Call`, which only this module used -/

section

/-! ### `MillerRabin.X86.CallResult`, which only this module used -/

section

/-! # The callable Montgomery postcondition gives the round's exact product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem mulPost {g : Geometry} {s t : State} {capacity b c : Nat}
    (ptrBound : g.W.toNat < 2 ^ 32) (capBound : capacity < 2 ^ 32) (bBound : b < 8)
    (a0 : arg s 0 = BitVec.ofNat 32 g.W.toNat) (a1 : arg s 1 = BitVec.ofNat 32 capacity)
    (a2 : arg s 2 = 6#32) (a3 : arg s 3 = 6#32) (a4 : arg s 4 = BitVec.ofNat 32 b)
    (M : Modulus g c s.mem) (odd : c % 2 = 1)
    (post : (Proof.Rsa.Mont.mulContract abi 56).post s t) :
    val32 t.mem g.W (g.array 6) g.words = Word32.mm c g.w
      (val32 s.mem g.W (g.array 6) g.words) (val32 s.mem g.W (g.array b) g.words) ∧
    Proof.Rsa.Mont.Keeps g.W capacity g.w 6 s.mem t.mem := by
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes] at post
  simp only [a0, a1, a2, a3, a4, ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound,
    Nat.mod_eq_of_lt (by omega_using [bBound] : b < 2 ^ 32), M.width] at post
  obtain ⟨low, congruence, keeps⟩ := post
  refine ⟨?_, keeps⟩
  rw [VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32] at low
  rw [VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32,
    VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32] at congruence
  change val32 t.mem g.W (g.array 6) g.words < val32 s.mem g.W (g.array 0) g.words at low
  change val32 t.mem g.W (g.array 6) g.words * 2 ^ (64 * g.w) % val32 s.mem g.W (g.array 0) g.words =
    val32 s.mem g.W (g.array 6) g.words * val32 s.mem g.W (g.array b) g.words %
      val32 s.mem g.W (g.array 0) g.words at congruence
  rw [M.candidate] at low congruence
  exact Word32.mm_eq odd low congruence

end VG.Proof.MillerRabin.X86

end

end


/-! # Actual Montgomery calls preserve the prepared round context -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mulCall_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {capacity b c : Nat} (length : g.L = 8 * capacity) (M : Modulus g c s.mem)
    (A : MulArguments g capacity b s) (right : Proof.Rsa.Mont.Operand b)
    (odd : c % 2 = 1) (rightLt : val32 s.mem g.W (g.array b) g.words < c)
    (fit : 80 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)) :
    WP isa (.frame (.push mulArgs) (.call name code) (.pop .eax 5)) s fun t =>
      val32 t.mem g.W (g.array 6) g.words = Word32.mm c g.w
        (val32 s.mem g.W (g.array 6) g.words) (val32 s.mem g.W (g.array b) g.words) ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Context g t ∧ Modulus g c t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below (s.gpr .esp) 80]) s.mem t.mem := by
  let rd : List Region := [⟨argAddr (pushed mulArgs s).callEntry 0, 20⟩]
  have rdEq : rd = [below (s.gpr .esp) 20] := by
    unfold rd
    rw [callEntry_argAddr0]
    rfl
  have cp : CallPre (Proof.Rsa.Mont.mulContract abi 56) mulArgs rd [⟨g.W, g.L⟩] s := by
    refine ⟨mulEntry_pre v C length M A right rightLt fit far, ?_, ?_⟩
    · rw [rdEq]
      apply Covers.of_mem
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact List.mem_append_right _ (List.mem_cons_self ..)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ C.ws.wr)
    · apply Covers.of_mem
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact List.mem_cons_of_mem _ C.ws.wr
  refine WP.callWith verified.1 noSp (by decide : mulArgs ≠ []) (by decide : Reg.esp ∉ mulArgs)
    (by change 20 + stackUse code + 4 ≤ _; omega_using [stack, fit]) cp ?_
  intro t rdT wrT saved frame post
  obtain ⟨u, mem, post⟩ := post
  have K : Keeps [.eax, .ecx, .edx] s t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp_all [calleeSaved]
  have far24 := far.sub_right (below_sub (by decide : 24 ≤ 80) fit)
  have F := mulEntry_frame (by omega_using [fit] : 24 ≤ (s.gpr .esp).toNat) C.ws.nowrap far24
  have Mu := M.keep v F (by simp) (by simp)
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := C.ws.nowrap; have := v.headerFit; omega_arith
  have capBound : capacity < 2 ^ 32 := by have := C.ws.nowrap; omega
  have sa := fun {i} (hi : i < 5) => mulEntry_arg A (by omega_using [fit]) hi
  obtain ⟨value, keeps⟩ := mulPost ptrBound capBound right.1
    (sa (by decide : 0 < 5)) (sa (by decide : 1 < 5)) (sa (by decide : 2 < 5))
    (sa (by decide : 3 < 5)) (sa (by decide : 4 < 5)) Mu odd post
  rw [mem] at value keeps
  have O : WorkspaceFrame g (montWrites g 6) s.mem t.mem :=
    (F.mono (by simp)).trans (montFrame length keeps)
  refine ⟨?_, O, K, C.keepMont v wrT (saved .edi (by decide)) O,
    M.keepMont v (by decide) O, VG.X86.Frame.below_mono frame (by change 20 + stackUse code + 4 ≤ 80; omega_using [stack]) fit⟩
  rw [value, F.val32 (v.arrayFit (by decide : 6 < 28)) (by simp),
    F.val32 (v.arrayFit (by have := right.1; omega_using [this])) (by simp)]

end VG.Proof.MillerRabin.X86

end

end


/-! # The round's multiplication operation reuses its prepared modulus -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem mulY_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {capacity b c : Nat} (length : g.L = 8 * capacity) (M : Modulus g c s.mem)
    (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1)
    (rightLt : val32 s.mem g.W (g.array b) g.words < c)
    (readLen : readSrc s (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity))
    (fit : 80 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)) :
    WP isa (mulY name code b) s fun t =>
      val32 t.mem g.W (g.array 6) g.words = Word32.mm c g.w
        (val32 s.mem g.W (g.array 6) g.words) (val32 s.mem g.W (g.array b) g.words) ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Context g t ∧ Modulus g c t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below (s.gpr .esp) 80]) s.mem t.mem := by
  unfold mulY
  refine WP.seq (WP.mono (mulSetup_ok C capacity b readLen) fun a ⟨A, M₁, K⟩ => ?_)
  have Ca := C.keepMem K (by decide) M₁
  have Ma : Modulus g c a.mem := by rw [M₁]; exact M
  have sp : a.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  refine WP.mono (mulCall_ok verified noSp stack v Ca length Ma A right odd
    (by rw [M₁]; exact rightLt) (by rw [sp]; exact fit) (by rw [sp]; exact far)) ?_
  rintro t ⟨V, O, Kt, Ct, Mt, F⟩
  rw [M₁] at V O F
  rw [sp] at F
  exact ⟨V, O, K.trans Kt, Ct, Mt, F⟩

end VG.Proof.MillerRabin.X86
