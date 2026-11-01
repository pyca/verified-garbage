module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The wrapper's initial domain-checking call -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

structure CheckFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Proof.Dsa.checkParametersContract X86.abi 108)
  noSp : NoSp code
  depth : stackUse code ≤ 108

def callWrites (s₀ : State) : List Region := callWr s₀ ++ [⟨rCall s₀, 112⟩]

def callResult (s₀ t : State) : Bool :=
  Spec.Dsa.checkParametersBytes (X86.arg s₀ 5).toNat (X86.arg s₀ 6).toNat
    (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat)

theorem call_covers {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    Covers (callRd s₀ ++ callWr s₀) (t.rd ++ t.wr) ∧ Covers (callWr s₀) t.wr := by
  have hF : (⟨rBase s₀, KeyRandom.frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self
  have hS : argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8) ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hK : argRegion s₀ 3 (X86.arg s₀ 4).toNat ∈ t.rd := by rw [h.rd, A.rd]; simp
  have hw : ∀ r ∈ callWr s₀, ∃ r' ∈ t.wr, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hS, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hF, 0, (BitVec.add_zero _).symm, by unfold KeyRandom.frameBytes; simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_append_left _ hK, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', o, ho⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

theorem call_ok (F : CheckFn) {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) :
    WP isa (.call F.name F.code) t fun u => Ready s₀ u ∧ Frame (callWrites s₀) t.mem u.mem ∧
      (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      u.gpr .eax = (if callResult s₀ t then 1 else 0) := by
  have he := esp_toNat A h
  have hfit := rLow_fit A (d := 192) (by decide)
  obtain ⟨hc, hcw⟩ := call_covers A h
  have hd := F.depth
  have hlo := A.stackLow
  have hrl := rLow_toNat A
  refine WP.call F.verified.1 F.noSp (by omega) (call_pre A h C) hc hcw
    fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have hesp : u.gpr .esp = t.gpr .esp := hcs .esp (by simp [calleeSaved])
  have hbelow : Region.Sub (below (t.gpr .esp) (stackUse F.code + 4)) ⟨rCall s₀, 112⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)).setWidth 64, _⟩ _
    rw [Taint.sub_setWidth (by omega), h.rf.esp, rBase, rLow_off, Offset.add_ofNat_sub _ (by omega)]
    exact Offset.sub_base _ (by omega)
  have hf' : Frame (callWrites s₀) t.mem u.mem := hf.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbelow⟩
  have hu : Ready s₀ u := by
    refine ⟨⟨by rw [hesp]; exact h.rf.esp, by rw [hwr]; exact h.rf.wr, by rw [hwr]; exact h.rf.args,
      h.rf.nowrap⟩, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans (hf'.sub fun r hr => ?_)⟩
    simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp [rWrites, rScratch], fun _ h => h⟩
    · exact ⟨rStack s₀, by simp [rWrites], stk_sub s₀ (by decide)⟩
    · refine ⟨rStack s₀, by simp [rWrites], ?_⟩
      have := Offset.sub_base (rCall s₀) (d := 0) (n := 112) (k := 232) (by decide)
      rwa [BitVec.add_zero] at this
  refine ⟨hu, hf', hcs, ?_⟩
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow] at hpost
  simp only [ce_arg A h C (callRd s₀) (callWr s₀) (show 0 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 1 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 2 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 3 < 6 by decide), callVal] at hpost
  rw [KeyRandom.callEntry_bytes A h (A.stackKeyWide.symm.sub_right (stk_sub s₀ (by decide))) (by omega),
    BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hpost
  apply BitVec.eq_of_toNat_eq
  change (u.gpr Reg.eax).toNat = _
  rw [hpost]
  change (if callResult s₀ t then 1 else 0) = _
  cases callResult s₀ t <;> rfl

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
