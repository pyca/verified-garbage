module

public import VerifiedGarbage.Proof.Dsa.X86.RandomCallPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Calling the supplied-nonce signer (x86)

`call_ok` runs the call of a verified `vg_dsa_sign` (`SignFn`) with the
arguments `callArgs` stored: it returns the signer's status, writes its
result to `out`, and changes memory only in `out`, `scratch`, the frame's
argument words and the stack below the frame.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- A verified `vg_dsa_sign`, for a frame of 20 bytes. -/
structure SignFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Spec.Dsa.signContract X86.abi 32)
  noSp : NoSp code
  depth : stackUse code ≤ 20

/-- Where the call may write. -/
def callWrites (s₀ : State) : List Region := callWr s₀ ++ [⟨rLow s₀, 24⟩]

/-- What the signer returns, from the bytes of the state `t` it is called in. -/
def callResult (s₀ t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (X86.arg s₀ 5).toNat (X86.arg s₀ 6).toNat
    (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat)
    (Spec.Rsa.bytesAt t.mem (off (rLow s₀) 112) (X86.arg s₀ 6).toNat)
    (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 7) (X86.arg s₀ 8).toNat)

theorem rBytes_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

/-- The return address's store leaves bytes apart from it. -/
theorem callEntry_bytes {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {p : Addr} {n : Nat}
    (hd : (Region.mk p n).Disjoint ⟨off (rLow s₀) 20, 4⟩) (hn : n ≤ 2 ^ 64) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW ((t.gpr .esp - 4).setWidth 64) v) p n = Spec.Rsa.bytesAt t.mem p n := by
  refine rBytes_frame (rs := [⟨off (rLow s₀) 20, 4⟩])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hn
  rw [esp_sub4 A h]
  have := Offset.contains_base (off (rLow s₀) 20) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

theorem call_covers {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    Covers (callRd s₀ ++ callWr s₀) (t.rd ++ t.wr) ∧ Covers (callWr s₀) t.wr := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hF : (⟨rBase s₀, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self
  have hO : argRegion s₀ 0 (X86.arg s₀ 1).toNat ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hS : argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8) ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hK : argRegion s₀ 3 (X86.arg s₀ 4).toNat ∈ t.rd := by rw [h.rd, A.rd]; simp
  have hD : argRegion s₀ 7 (X86.arg s₀ 8).toNat ∈ t.rd := by rw [h.rd, A.rd]; simp
  have hw : ∀ r ∈ callWr s₀, ∃ r' ∈ t.wr, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hO, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hS, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hF, 0, (BitVec.add_zero _).symm, by unfold Random.frameBytes; simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ hK, 0, (BitVec.add_zero _).symm, by simp⟩
    · refine ⟨_, List.mem_append_right _ hF, 88, ?_, ?_⟩
      · show off (rLow s₀) 112 = off (rLow s₀) 24 + BitVec.ofNat 64 88
        rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · show 88 + (X86.arg s₀ 6).toNat ≤ Random.frameBytes
        unfold Random.frameBytes; omega
    · exact ⟨_, List.mem_append_left _ hD, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', o, ho⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

theorem call_ok (F : SignFn) {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) :
    WP isa (.call F.name F.code) t fun u => Ready s₀ u ∧ Frame (callWrites s₀) t.mem u.mem ∧
      (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      u.gpr .eax = BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ t)) ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
        (callResult s₀ t).getD (List.replicate (X86.arg s₀ 1).toNat 0) := by
  have he := esp_toNat A h
  have hfit := rLow_fit A (d := 200) (by decide)
  obtain ⟨hc, hcw⟩ := call_covers A h
  have hd := F.depth
  refine WP.call F.verified.1 F.noSp (by omega) (call_pre A h C) hc hcw
    fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have hesp : u.gpr .esp = t.gpr .esp := hcs .esp (by simp [calleeSaved])
  -- Where the call wrote.
  have hbelow : Region.Sub (below (t.gpr .esp) (stackUse F.code + 4)) ⟨rLow s₀, 24⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)).setWidth 64, _⟩ _
    rw [Taint.sub_setWidth (by omega), h.rf.esp, rBase, Offset.add_ofNat_sub _ (by omega)]
    exact Offset.sub_base _ (by omega)
  have hf' : Frame (callWrites s₀) t.mem u.mem := hf.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbelow⟩
  have hu : Ready s₀ u := by
    refine ⟨⟨by rw [hesp]; exact h.rf.esp, by rw [hwr]; exact h.rf.wr, by rw [hwr]; exact h.rf.args,
      h.rf.nowrap⟩, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans (hf'.sub fun r hr => ?_)⟩
    simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [rWrites, rOut], fun _ h => h⟩
    · exact ⟨_, by simp [rWrites, rScratch], fun _ h => h⟩
    · exact ⟨rStack s₀, by simp [rWrites], stk_sub s₀ (by decide)⟩
    · refine ⟨rStack s₀, by simp [rWrites], ?_⟩
      have := Offset.sub_base (rLow s₀) (d := 0) (n := 24) (k := 144) (by decide)
      rwa [BitVec.add_zero] at this
  refine ⟨hu, hf', hcs, ?_⟩
  -- The signer's postcondition.
  have hp := hpost
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at hp
  simp only [ce_arg A h C (callRd s₀) (callWr s₀) (show 0 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 1 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 2 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 3 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 4 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 5 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 6 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 7 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 8 < 11 by decide),
    callVal, esp_ptr h (d := oNonce) (by decide), show 24 + oNonce = 112 from rfl] at hp
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  rw [callEntry_bytes A h (A.stackKey.symm.sub_right (stk_sub s₀ (by decide))) (by omega),
    callEntry_bytes A h ((Offset.disjoint _ (by omega) (by omega) (by omega) :
      Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩).symm) (by omega),
    callEntry_bytes A h (A.stackDigest.symm.sub_right (stk_sub s₀ (by decide))) (by omega)] at hp
  obtain ⟨hr, hb⟩ := hp
  refine ⟨?_, by rw [← hm₂]; exact hb⟩
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  apply BitVec.eq_of_toNat_eq
  rw [hr, toNat_ofNat_lt (by unfold Spec.Dsa.signStatus; split <;> decide)]
  rfl

end VG.Proof.Dsa.X86
