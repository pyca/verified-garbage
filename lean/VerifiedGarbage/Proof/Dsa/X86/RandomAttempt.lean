module

public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
public import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
public import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.X86.RandomAttemptState`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RandomCall`, which this module and modules that import it used -/

section

/-!
# Calling the supplied-nonce signer (x86)

`call_ok` runs the call of a verified supplied-nonce signer (`SignFn`), for a
key it accepts, with the arguments `callArgs` stored: it returns the signer's status, writes its
result to `out`, and changes memory only in `out`, `scratch`, the frame's
argument words and the stack below the frame.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- A supplied-nonce signer the randomized wrapper calls, for a frame of 20
bytes: the fully checked `vg_dsa_sign` (`valid` always true), or
`vg_dsa_sign_prevalidated` (`valid` is `validatePrivateKeyBytes`). It is
verified against `signContract` under `valid` of the exact key bytes it is
called with. -/
structure SignFn where
  name : String
  code : Prog isa
  valid : Nat → Nat → List Byte → Bool
  verified : Verified X86.target code (signContractWith valid X86.abi 108)
  noSp : NoSp code
  depth : stackUse code ≤ 108

/-- The signer's validity of the wrapper's key. -/
def KeyValid (valid : Nat → Nat → List Byte → Bool) (s₀ : State) : Prop :=
  valid (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key = true

theorem signWith_pre {valid : Nat → Nat → List Byte → Bool} {s : State}
    (h : (signContractWith valid abi 108).pre s) :
    (Spec.Dsa.signContract abi 108).pre s ∧
      valid (X86.arg s 4).toNat (X86.arg s 6).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (X86.arg s 3).toNat) = true := by
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros <;> with_reducible assumption

theorem signWith_of_pre {valid : Nat → Nat → List Byte → Bool} {s : State}
    (h : (Spec.Dsa.signContract abi 108).pre s)
    (hv : valid (X86.arg s 4).toNat (X86.arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (X86.arg s 3).toNat) = true) :
    (signContractWith valid abi 108).pre s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_split h
  sig_and_intros <;> with_reducible assumption

/-- Where the call may write. -/
def callWrites (s₀ : State) : List Region := callWr s₀ ++ [⟨rCall s₀, 112⟩]

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

/-- The key's bytes, while the frame is allocated. -/
theorem callKey {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKeyWide.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

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

/-- The signer's contract at the wrapper's call boundary, for a key the
signer accepts. -/
theorem call_pre_with {valid : Nat → Nat → List Byte → Bool} {s₀ t : State} (A : RandomSignABI s₀)
    (h : Ready s₀ t) (C : CallSlots s₀ t) (hv : KeyValid valid s₀) :
    (signContractWith valid abi 108).pre (t.callEntry.withRegions (callRd s₀) (callWr s₀)) := by
  refine signWith_of_pre (call_pre A h C) ?_
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hp : argumentPointer (t.callEntry.withRegions (callRd s₀) (callWr s₀)) 2 = argumentPointer s₀ 3 := by
    simp only [argumentPointer, ce_arg A h C (callRd s₀) (callWr s₀) (show 2 < 11 by decide), callVal]
  have hk : Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s₀) (callWr s₀)).mem (argumentPointer s₀ 3)
      (X86.arg s₀ 4).toNat = (rInput s₀).key :=
    (callEntry_bytes A h (A.stackKeyWide.symm.sub_right (stk_sub s₀ (by decide))) (by omega_using []) _).trans (callKey A h)
  rw [ce_arg A h C (callRd s₀) (callWr s₀) (show 3 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 4 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 6 < 11 by decide), hp]
  simp only [callVal]
  rw [hk]
  exact hv

theorem call_ok (F : SignFn) {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t)
    (hv : KeyValid F.valid s₀) :
    WP isa (.call F.name F.code) t fun u => Ready s₀ u ∧ Frame (callWrites s₀) t.mem u.mem ∧
      (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      u.gpr .eax = BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ t)) ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
        (callResult s₀ t).getD (List.replicate (X86.arg s₀ 1).toNat 0) := by
  have he := esp_toNat A h
  have hfit := rLow_fit A (d := 200) (by decide)
  obtain ⟨hc, hcw⟩ := call_covers A h
  have hd := F.depth
  have hlo := A.stackLow
  have hrl := rLow_toNat A
  refine WP.call F.verified.1 F.noSp (by omega_using [he, hd, hlo, hrl]) (call_pre_with A h C hv) hc hcw
    fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have hesp : u.gpr .esp = t.gpr .esp := hcs .esp (by simp [calleeSaved])
  -- Where the call wrote.
  have hbelow : Region.Sub (below (t.gpr .esp) (stackUse F.code + 4)) ⟨rCall s₀, 112⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)).setWidth 64, _⟩ _
    rw [Taint.sub_setWidth (by omega_using [he, hd, hlo, hrl]), h.rf.esp, rBase, rLow_off, Offset.add_ofNat_sub _ (by omega_using [hd])]
    exact Offset.sub_base _ (by omega_using [hd])
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
      have := Offset.sub_base (rCall s₀) (d := 0) (n := 112) (k := 232) (by decide)
      rwa [BitVec.add_zero] at this
  refine ⟨hu, hf', hcs, ?_⟩
  -- The signer's postcondition.
  have hp := hpost
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at hp
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
  rw [callEntry_bytes A h (A.stackKeyWide.symm.sub_right (stk_sub s₀ (by decide))) (by omega_using []),
    callEntry_bytes A h ((Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using []) :
      Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩).symm) (by omega_using []),
    callEntry_bytes A h (A.stackDigestWide.symm.sub_right (stk_sub s₀ (by decide))) (by omega_using [])] at hp
  obtain ⟨hr, hb⟩ := hp
  refine ⟨?_, by rw [← hm₂]; exact hb⟩
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  apply BitVec.eq_of_toNat_eq
  rw [hr, toNat_ofNat_lt (by unfold Spec.Dsa.signStatus; split <;> decide)]
  rfl

end VG.Proof.Dsa.X86

end

end

/-!
# The signer's state between attempts (x86)

`Att`: the sampler's state, the attempts left, the callee-saved registers
in their slots, and how the rest of the specification's signing loop
(`randomSignRemaining`) gives the overall result (`rResult`). `Done`: the
loop's status and consumption, and the signature in `out` on success.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The overall result. -/
abbrev rResult (s₀ : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest
    (rInput s₀).rand

/-- The callee-saved registers, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  slot m (rBase s₀) oSaveEbx = s₀.gpr .ebx ∧ slot m (rBase s₀) oSaveEsi = s₀.gpr .esi ∧
    slot m (rBase s₀) oSaveEdi = s₀.gpr .edi ∧ slot m (rBase s₀) oSaveEbp = s₀.gpr .ebp

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, 44 ≤ d → d + 4 ≤ 60 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨(he _ (by decide) (by decide)).trans h.1, (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2⟩

/-- The spec's signing from `used` on, with `fuel` attempts left, gives the
overall result. -/
abbrev RRel (s₀ : State) (used fuel : Nat) : Prop :=
  VG.Proof.Dsa.RandomSignResultRel (rInput s₀) 0 (rResult s₀) used fuel

/-- Between attempts. -/
structure Att (s₀ : State) (used fuel : Nat) (t : State) : Prop where
  smp : ∃ d, Smp s₀ used d t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 fuel
  saved : Saved s₀ t.mem
  rel : RRel s₀ used fuel

/-- After the attempts. -/
structure Done (s₀ : State) (t : State) : Prop where
  smp : ∃ d, Smp s₀ (rResult s₀).used d t
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
    (rResult s₀).signature.getD (List.replicate (X86.arg s₀ 1).toNat 0)
  saved : Saved s₀ t.mem

/-! ## What the call keeps -/

theorem self_contains (x : Addr) : (⟨x, 1⟩ : Region).Contains x 1 := by
  simp [Region.Contains]

/-- The frame above its argument words is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : RandomSignABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d < 120) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  rw [rBase_off, rLow_off]
  have hs : (rStack s₀).Contains (off (rCall s₀) (88 + (24 + d))) 1 := Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
  refine hf _ fun r hr => ?_
  simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackOutWide _ hs
  · exact A.stackScratchWide _ hs
  · rw [rLow_off]
    exact (Offset.disjoint (rCall s₀) (d := 88 + (24 + d)) (n := 1) (e := 88 + 24) (k := 44) (by omega_using [h₁])
      (by omega_using [h₂]) (by omega_using [])) _ (self_contains _)
  · exact (Offset.disjoint_base (rCall s₀) (d := 88 + (24 + d)) (n := 1) (k := 112) (by omega_using []) (by omega_using [h₂])) _
      (self_contains _)

theorem call_frame_slot {s₀ : State} (A : RandomSignABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega_using [h₁]) (by omega_using [h₂, hi])

/-- The call keeps the sampler's state. -/
theorem Smp.after_call {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hf : Frame (callWrites s₀) t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, S.usedBound⟩
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.q
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.width
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.mask
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.usedW
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.drawsW
  · rw [call_frame_byte A hf (by unfold oNonce; omega_using []) (by unfold oNonce; omega_using [hql, hi])]; exact S.pad i hi

/-- The argument stores keep the sampler's state. -/
theorem Smp.after_args {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) [(0, 44)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hs : ∀ d, 44 ≤ d → d + 4 ≤ 120 → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₁ h₂ =>
    slot_outs hm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; right; exact h₁) (by omega_using [h₂])
  refine ⟨hr, (hs _ (by decide) (by decide)).trans S.q, (hs _ (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  rw [hm _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold oNonce; omega_using [hql, hi])]; right; unfold oNonce; omega_using []]
  exact S.pad i hi

end VG.Proof.Dsa.X86

end

end

/-!
# One signing attempt (x86)

`attempt` samples a nonce and, if one is accepted, calls the signer with it
(`call_ok`): a signature ends the attempts, a failure spends one. As the
specification's `randomSignLoop` does (`RandomSignResultRel`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

/-- Record the signer's status `st`, and test it. -/
theorem finHead_ok {s₀ u : State} (h : Ready s₀ u) {st : Nat} (hst : st ≤ 1)
    (he : u.gpr .eax = BitVec.ofNat 32 st) :
    WP isa (.block [.store (sp oStatus) .eax, .alu .cmp .eax (.imm 0)]) u fun v => Ready s₀ v ∧
      Keeps [.eax] u v ∧ v.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 st) ∧
      v.zf = some (decide (st = 0)) := by
  refine wp_slot h.rf (by decide) he fun v₁ f₁ m₁ g₁ r₁ w₁ _ _ => wp_cmpi fun v₂ fv₂ _ z₂ => WP.block_nil ?_
  obtain k₂ : Keeps [.eax] u v₂ := Keeps.trans (⟨fun r _ => by rw [g₁], r₁, w₁⟩ : Keeps [.eax] u v₁) (fv₂.keeps _)
  obtain m₂ : v₂.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 st) := by rw [fv₂.mem, m₁]
  obtain h₂ : Ready s₀ v₂ := h.congr k₂ (by rw [m₂]; exact frame_store s₀ _ (by decide) _)
  rw [g₁, he, show (BitVec.ofNat 32 st - 0 : BitVec 32) = BitVec.ofNat 32 st - BitVec.ofNat 32 0 from rfl,
    sub_beq (by omega_using [hst]) (by decide)] at z₂
  exact ⟨h₂, k₂, m₂, z₂⟩

/-- Spend an attempt. -/
theorem finDec_ok {s₀ v₂ : State} (h₂ : Ready s₀ v₂) {f : Nat}
    (ha : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) (hf : f + 1 ≤ 8) :
    WP isa (.block [.mov .eax (.mem (sp oAttempts)), .alu .sub .eax (.imm 1), .store (sp oAttempts) .eax]) v₂
      fun v₅ => Ready s₀ v₅ ∧ Keeps [.eax] v₂ v₅ ∧
        v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) ∧ v₅.zf = some (decide (f = 0)) := by
  refine wp_movS (v := BitVec.ofNat 32 (f + 1)) (by rw [h₂.rf.readSlot (by decide)]; exact congrArg some ha)
    fun v₃ u₃ _ => wp_subi fun v₄ u₄ _ z₄ => ?_
  obtain e₄ : v₄.gpr .eax = BitVec.ofNat 32 f := by
    rw [u₄.gpr, u₃.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_using [])]; rfl
  obtain f₄ := h₂.rf.of_keeps ((u₃.keeps.mono (by decide)).trans u₄.keeps)
  refine wp_slot f₄ (by decide) e₄ fun v₅ f₅ m₅ g₅ r₅ w₅ zf₅ _ => WP.block_nil ?_
  obtain k₅ : Keeps [.eax] v₂ v₅ := ((u₃.keeps.mono (by decide)).trans u₄.keeps).trans
    ⟨fun r _ => by rw [g₅], r₅, w₅⟩
  obtain hm₅ : v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) := by
    rw [m₅, u₄.mem, u₃.mem]
  obtain h₅ : Ready s₀ v₅ := h₂.congr (rs := [.eax]) ((u₃.keeps.trans u₄.keeps).trans ⟨fun r _ => by rw [g₅], r₅, w₅⟩)
    (by rw [hm₅]; exact frame_store s₀ _ (by decide) _)
  obtain z₅ : v₅.zf = some (decide (f = 0)) := by
    rw [zf₅, z₄, u₃.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_using [hf]) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_using []))
  exact ⟨h₅, k₅, hm₅, z₅⟩

/-- Record the signer's status `st`, and spend an attempt on a failure. -/
theorem callFinish_ok {s₀ u : State} (h : Ready s₀ u) {st f : Nat} (hst : st ≤ 1)
    (he : u.gpr .eax = BitVec.ofNat 32 st) (ha : slot u.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1))
    (hf : f + 1 ≤ 8) :
    WP isa callFinish u fun v => Ready s₀ v ∧ Keeps [.eax] u v ∧
      Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v.mem ∧
      (st = 1 → slot v.mem (rBase s₀) oStatus = 1 ∧ slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) ∧
      (st = 0 → slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 f ∧
        slot v.mem (rBase s₀) oStatus = (if f = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (finHead_ok h hst he) fun v₂ ⟨h₂, k₂, m₂, z₂⟩ => ?_)
  obtain o₂ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₂.mem := by
    rw [m₂]; exact store_outs _ _ _ (by decide)
  by_cases h0 : st = 0
  · subst h0
    refine WP.ite true (by simp only [eval, z₂, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    obtain ha₂ : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha
    refine WP.seq (WP.mono (finDec_ok h₂ ha₂ hf) fun v₅ ⟨h₅, k₅', hm₅, z₅⟩ => ?_)
    obtain k₅ : Keeps [.eax] u v₅ := k₂.trans k₅'
    obtain o₅ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₅.mem := by
      rw [hm₅]; exact o₂.trans (store_outs _ _ _ (by decide))
    by_cases hf0 : f = 0
    · refine WP.ite false (by simp only [eval, z₅, hf0, decide_true, Option.map_some, Bool.not_true])
        (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨h₅, k₅, o₅, fun e => absurd e (by decide), fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₅, slot_write_self]
      · rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide), m₂, slot_write_self, hf0]; rfl
    · refine WP.ite true (by simp only [eval, z₅, hf0, decide_false, Option.map_some, Bool.not_false])
        (fun _ => wp_movS rfl fun v₆ u₆ _ => wp_slot (h₅.rf.of_keeps u₆.keeps) (by decide) u₆.gpr
          fun v₇ f₇ m₇ g₇ r₇ w₇ _ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      obtain hm₇ : v₇.mem = v₅.mem.writeW (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₇, u₆.mem]
      refine ⟨h₅.congr (rs := [.eax]) (u₆.keeps.trans ⟨fun r _ => by rw [g₇], r₇, w₇⟩)
          (by rw [hm₇]; exact frame_store s₀ _ (by decide) _),
        (k₅.trans u₆.keeps).trans ⟨fun r _ => by rw [g₇], r₇, w₇⟩,
        by rw [hm₇]; exact o₅.trans (store_outs _ _ _ (by decide)), fun e => absurd e (by decide),
        fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide), hm₅, slot_write_self]
      · rw [hm₇, slot_write_self]; simp only [hf0, ↓reduceIte]
  · have h1 : st = 1 := by omega_using [hst, h0]
    subst h1
    refine WP.ite false (by simp only [eval, z₂]; rfl) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
    refine ⟨h₂, k₂, o₂, fun _ => ⟨?_, ?_⟩, fun e => absurd e (by decide)⟩
    · rw [m₂, slot_write_self]; rfl
    · rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha

/-- Slot stores keep the sampler's state. -/
theorem Smp.after_finish {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] t.mem u.mem) : Smp s₀ used d u := by
  obtain hql := rQBytes_le A
  obtain hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  obtain hs : ∀ d, d ≤ 120 → (d + 4 ≤ oAttempts ∨ oAttempts + 4 ≤ d) → (d + 4 ≤ oStatus ∨ oStatus + 4 ≤ d) →
      slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₀ h₁ h₂ =>
    slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂) (by omega_using [h₀])
  refine ⟨hr, (hs _ (by decide) (by decide) (by decide)).trans S.q,
    (hs _ (by decide) (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  obtain hle : ∀ r ∈ ([(oAttempts, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
  rw [hm _ fun r hr => by
    have := hle r hr
    rw [ofs_off0 _ (by unfold oNonce; omega_using [hql, hi])]
    right; omega_using [this]]
  exact S.pad i hi

/-- Stores to the frame keep bytes apart from the stack. -/
theorem frameOuts_bytes {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (hm : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 120) {p : Addr} {n : Nat}
    (hd : (rStack s₀).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  refine hm _ fun r hr => ?_
  obtain hb := hrs r hr
  by_cases hx : ofs (rBase s₀) (p + BitVec.ofNat 64 i) < 120
  · exfalso
    refine hd _ ?_ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_using [hi]) (by omega_using [hn, hi]))
    obtain he : p + BitVec.ofNat 64 i = off (rBase s₀) (ofs (rBase s₀) (p + BitVec.ofNat 64 i)) := by
      simp only [ofs, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm (rBase s₀), BitVec.sub_add_cancel]
    rw [he, rBase_off, rLow_off]
    exact Offset.contains_base _ (by omega_using [hx]) (by omega_using [hx])
  · right; omega_using [hb, hx]

/-- The signer's input is the specification's, with the sampled nonce. -/
theorem callResult_eq {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length k) :
    callResult s₀ t = Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest := by
  obtain hqn := rQBytes_length A
  obtain hkey := callKey A h
  obtain hdig : Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 7) (X86.arg s₀ 8).toNat = (rInput s₀).digest := by
    refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.stackDigestWide.symm
    · exact A.outDigest.symm
    · exact A.digestScratch
    · exact A.usedDigest.symm
  obtain hnon : Spec.Rsa.bytesAt t.mem (off (rLow s₀) 112) (X86.arg s₀ 6).toNat =
      Spec.Dsa.encodeBE (rInput s₀).qLen k := by
    rw [show off (rLow s₀) 112 = off (rBase s₀) oNonce from (rBase_off s₀ oNonce).symm, ← hqn, hn, hqn]; rfl
  unfold callResult
  rw [hkey, hdig, hnon]; rfl

/-- Slots below the ranges that changed. -/
theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

/-- Slots above the ranges that changed. -/
theorem outs_high {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ e) {d : Nat} (hd : e ≤ d) (hd' : d + 4 < 2 ^ 64) :
    slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inr (Nat.le_trans (hrs r hr) hd)) hd'

/-- Bytes of the frame above the ranges that changed. -/
theorem outs_frame_bytes {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d n : Nat}
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ d) (hd : d + n < 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off B d) n = Spec.Rsa.bytesAt m (off B d) n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact h _ fun r hr => by
    have := hrs r hr
    rw [ofs_off B (by omega_using [hd, hi])]; right; omega_using [this]

/-- What an attempt from `used` with `f + 1` attempts left leaves: another
attempt to make after a retry, which its signing trace records, or the result. -/
def AttemptOut (s₀ : State) (used f : Nat) (u : State) : Prop :=
  (slot u.mem (rBase s₀) oStatus = 4 ∧ 1 ≤ f ∧ Att s₀ (used + (spl s₀ 128 used).used) f u ∧
    VG.Proof.Dsa.randomSigningTrace (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace =
      6 :: (VG.Proof.Dsa.randomSignRemaining (rInput s₀) (used + (spl s₀ 128 used).used) f).trace) ∨
    (slot u.mem (rBase s₀) oStatus ≠ 4 ∧ Done s₀ u ∧
      ¬ ((VG.Proof.Dsa.randomSigningTrace
        (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace).head? = some 6 ∧ 1 ≤ f))

theorem attempt_ok (F : SignFn) {s₀ t : State} (A : RandomSignABI s₀) {used f : Nat}
    (T : Att s₀ used (f + 1) t) (hf : f + 1 ≤ 8) (hq : 1 < rq s₀) (hv : KeyValid F.valid s₀) :
    WP isa (attempt F.name F.code) t fun u => AttemptOut s₀ used f u := by
  obtain hql := rQBytes_le A
  obtain ⟨d₀, Sm⟩ := T.smp
  unfold attempt
  refine WP.seq (WP.mono (sample_ok A Sm hq) fun u₁ ⟨O, eax₁, h₁, o₁, _⟩ => ?_)
  obtain sv₁ : Saved s₀ u₁.mem := T.saved.of_slots fun d _ hd => outs_low o₁ (by decide) hd (by omega_using [hd])
  obtain at₁ : slot u₁.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) :=
    (slot_outs o₁ (by decide) (by decide)).trans T.attempts
  refine WP.seq (wp_cmpi fun u₂ fv₂ _ z₂ => WP.block_nil ?_)
  obtain h₂ := h₁.fupd fv₂
  have m₂ : u₂.mem = u₁.mem := fv₂.mem
  obtain hle := sampleStatus_le (spl s₀ 128 used)
  rw [eax₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_using [hle]) (by decide)] at z₂
  cases hsc : (spl s₀ 128 used).scalar with
  | none =>
    obtain hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]; split <;> simp
    refine WP.ite false (by simp only [eval, z₂, hst, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    obtain ⟨-, hstat, hused⟩ := T.rel.sample_none hsc
    obtain ⟨d', S'⟩ := O.smp
    refine .inr ⟨?_, ⟨⟨d', ?_⟩, ?_, fun e => absurd (hstat ▸ e) hst, (by rw [m₂]; exact sv₁)⟩,
      by rw [VG.Proof.Dsa.random_sign_trace_none _ _ _ hsc]; simp⟩
    · rw [m₂, O.status]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_lt (by omega_using [hle])] at this
      exact absurd this (by show _ ≠ 4; omega_using [hle])
    · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
      rw [e]; exact S'.mem A h₂ m₂
    · rw [m₂, O.status]; exact congrArg (BitVec.ofNat 32) hstat.symm
  | some k =>
    obtain hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]
    refine WP.ite true (by simp only [eval, z₂, hst, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    obtain ⟨d', S'⟩ := O.smp
    obtain S₂ := S'.mem A h₂ m₂
    refine WP.seq (?_ : WP isa (.block (callArgs ++ [])) u₂ _)
    refine callArgs_ok A h₂ fun u₃ h₃ m₃ k₃ => WP.block_nil ?_
    obtain o₃ := argsMem_outs s₀ u₂.mem (u₂.gpr .esp)
    rw [← m₃] at o₃
    obtain C₃ : CallSlots s₀ u₃ := fun i hi => by
      rw [m₃, k₃.1 .esp (by decide)]; exact argsMem_slots s₀ _ _ i hi
    obtain hk : Spec.Rsa.bytesAt u₃.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
        Spec.Dsa.encodeBE (rQBytes s₀).length k := by
      rw [outs_frame_bytes o₃ (by decide) (by unfold oNonce; omega_using [hql]), m₂]; exact O.nonce k hsc
    obtain hres := callResult_eq A h₃ hk
    refine WP.seq (WP.mono (call_ok F A h₃ C₃ hv) fun u₄ ⟨h₄, f₄, _, eax₄, out₄⟩ => ?_)
    obtain at₄ : slot u₄.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [call_frame_slot A f₄ (by decide) (by decide), outs_high o₃ (e := 44) (by decide) (by decide) (by decide), m₂]
      exact at₁
    obtain S₄ := (S₂.after_args A h₃ o₃).after_call A h₄ f₄
    obtain sv₄ : Saved s₀ u₄.mem := sv₁.of_slots fun d h₁ hd => by
      rw [call_frame_slot A f₄ h₁ (by omega_using [hd]), outs_high o₃ (e := 44) (by decide) h₁ (by omega_using [hd]), m₂]
    rw [hres] at eax₄ out₄
    refine WP.mono (callFinish_ok h₄ (by unfold Spec.Dsa.signStatus; split <;> decide) eax₄ at₄ hf)
      fun u₅ ⟨h₅, _, o₅, hT1, hT0⟩ => ?_
    obtain S₅ := S₄.after_finish A h₅ o₅
    obtain sv₅ : Saved s₀ u₅.mem := sv₄.of_slots fun d _ hd => outs_low o₅ (by decide) hd (by omega_using [hd])
    cases hsb : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
    | some sig =>
      obtain ⟨st₅, -⟩ := hT1 (by rw [hsb]; rfl)
      obtain ⟨hsig, hstat, hused⟩ := T.rel.success hsc hsb
      refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun _ => ?_, sv₅⟩,
        by rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hsc hsb]; simp⟩
      · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · rw [frameOuts_bytes o₅ (by decide) A.stackOutWide (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
          (by decide))), out₄, hsb, hsig]
    | none =>
      obtain ⟨at₅, st₅⟩ := hT0 (by rw [hsb]; rfl)
      obtain R' := T.rel.retry hsc hsb
      by_cases hf0 : f = 0
      · subst hf0
        obtain ⟨-, hstat, hused⟩ := R'.exhausted
        refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun e => absurd e (by omega_using [hstat]), sv₅⟩,
          fun h => absurd h.2 (by decide)⟩
        obtain e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · refine .inl ⟨by rw [st₅]; simp only [hf0, ↓reduceIte], by omega_using [hf0], ⟨⟨d', S₅⟩, at₅, sv₅, R'⟩,
          ?_⟩
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega_using [hf0]⟩
        exact VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hsc hsb

end VG.Proof.Dsa.X86
