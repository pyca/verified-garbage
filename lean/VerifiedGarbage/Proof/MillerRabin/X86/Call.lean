module

public import VerifiedGarbage.Proof.MillerRabin.X86.CallEntry
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MillerRabin.X86.CallPre
import VerifiedGarbage.Proof.MillerRabin.X86.CallResult
import VerifiedGarbage.Proof.Framework.X86.CallWith

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
    (by change 20 + stackUse code + 4 ≤ _; omega) cp ?_
  intro t rdT wrT saved frame post
  obtain ⟨u, mem, post⟩ := post
  have K : Keeps [.eax, .ecx, .edx] s t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp_all [calleeSaved]
  have far24 := far.sub_right (below_sub (by decide : 24 ≤ 80) fit)
  have F := mulEntry_frame (by omega : 24 ≤ (s.gpr .esp).toNat) C.ws.nowrap far24
  have Mu := M.keep v F (by simp) (by simp)
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := C.ws.nowrap; have := v.headerFit; omega
  have capBound : capacity < 2 ^ 32 := by have := C.ws.nowrap; omega
  have sa := fun {i} (hi : i < 5) => mulEntry_arg A (by omega) hi
  obtain ⟨value, keeps⟩ := mulPost ptrBound capBound right.1
    (sa (by decide : 0 < 5)) (sa (by decide : 1 < 5)) (sa (by decide : 2 < 5))
    (sa (by decide : 3 < 5)) (sa (by decide : 4 < 5)) Mu odd post
  rw [mem] at value keeps
  have O : WorkspaceFrame g (montWrites g 6) s.mem t.mem :=
    (F.mono (by simp)).trans (montFrame length keeps)
  refine ⟨?_, O, K, C.keepMont v wrT (saved .edi (by decide)) O,
    M.keepMont v (by decide) O, VG.X86.Frame.below_mono frame (by change 20 + stackUse code + 4 ≤ 80; omega) fit⟩
  rw [value, F.val32 (v.arrayFit (by decide : 6 < 28)) (by simp),
    F.val32 (v.arrayFit (by have := right.1; omega)) (by simp)]

end VG.Proof.MillerRabin.X86
