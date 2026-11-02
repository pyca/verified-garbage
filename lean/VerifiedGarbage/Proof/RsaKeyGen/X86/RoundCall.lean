module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundPre
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame

/-! # Reuse a verified Miller–Rabin round without rebuilding candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

theorem call_ok {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) (A : Arguments g capacity s)
    (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (call name round) s fun t =>
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  let rd : List Region := [⟨argAddr (pushed args s).callEntry 0, 8⟩]
  have rdEq : rd = [below (s.gpr .esp) 8] := by
    unfold rd
    rw [callEntry_argAddr0]
    rfl
  have cp : CallPre (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) args rd [⟨g.W, g.L⟩] s := by
    refine ⟨entry_pre v length S A odd large witness (by rw [S.ready.caller.sp]; exact fit)
      (by rw [S.ready.caller.sp]; exact far), ?_, ?_⟩
    · rw [rdEq]
      apply Covers.of_mem
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact List.mem_append_right _ (List.mem_cons_self ..)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ S.ready.context.ws.wr)
    · apply Covers.of_mem
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact List.mem_cons_of_mem _ S.ready.context.ws.wr
  refine WP.callWithReturn verified.1 noSp (by decide : args ≠ []) (by decide : Reg.esp ∉ args)
    (by rw [S.ready.caller.sp]; change 8 + stackUse round + 4 ≤ _; omega) cp ?_
  intro t rdT wrT saved frame post
  obtain ⟨u, mem, reg, post⟩ := post
  have K : Keeps [.eax, .ecx, .edx] s t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp_all [calleeSaved]
  have far12 := far.sub_right (below_sub (by decide : 12 ≤ 108) fit)
  have F := entry_frame (by rw [S.ready.caller.sp]; omega) S.ready.scratch.nowrap
    (by rw [S.ready.caller.sp]; exact far12)
  have Mu := S.ready.modulus.keep v F (by simp) (by simp)
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := S.ready.scratch.nowrap; have := v.headerFit; omega
  have capBound : capacity < 2 ^ 32 := by have := S.ready.scratch.nowrap; omega
  have sa := fun {i} (hi : i < 2) => entry_arg A (by rw [S.ready.caller.sp]; omega) hi
  obtain ⟨value, keeps⟩ := roundPost ptrBound capBound (sa (by decide)) (sa (by decide)) Mu
    ((F.val32 (v.arrayFit (by decide)) (by simp)).trans witness) post
  rw [mem] at keeps
  rw [reg] at value
  have W : WorkspaceFrame g (roundWrites g) s.mem t.mem :=
    (F.mono (by simp)).trans (reviewed_frame length keeps)
  have G : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem := by
    rw [← S.ready.caller.sp]
    exact VG.X86.Frame.below_mono frame (by change 8 + stackUse round + 4 ≤ 108; omega)
      (by rw [S.ready.caller.sp]; exact fit)
  exact ⟨data_keep v S K W G lengthFar, value, W, G, K⟩

theorem code_ok {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (code name round) s fun t =>
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold code
  refine WP.seq (wp_movS S.ready.caller.readLen fun a A _ => WP.block_nil ?_)
  have Da := WitnessMont.data_outside v S
    (show Outside g.W (g.array 6) (4 * g.words) s.mem a.mem from by rw [A.mem]; exact Outside.refl _ _ _ _)
    A.keeps (by decide) (by decide)
  have callArgs : Arguments g capacity a := by
    refine ⟨?_, A.gpr⟩
    apply BitVec.eq_of_toNat_eq
    rw [A.other .edi (by decide), S.ready.scratch.edi_toNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := S.ready.scratch.nowrap; have := v.headerFit; omega)).symm
  refine WP.mono (call_ok (b := b) verified noSp stack v length Da callArgs odd large (by rw [A.mem]; exact witness)
    fit far lengthFar) fun t ⟨D, result, W, F, K⟩ => ?_
  rw [A.mem] at W F
  exact ⟨D, result, W, F, (A.keeps.mono (by decide)).trans K⟩

end VG.Proof.RsaKeyGen.X86.RoundCall
