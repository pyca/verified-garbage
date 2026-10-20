module
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallPre
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Layout

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Safety

/-! # One attempt of the key-generation controller

In its frame, the controller passes `vg_ffdh_generate_key` the next `p_len`
octets of the tape. The attempt keeps the controller's state, and leaves
its status, and the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame_size allocated freed
  allocated_rsp allocated_reg freed_rsp freed_reg frame_alloc)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkPost generateCode generateCode_sp)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus p.a p.len (rand.drop used)
  let x := Spec.Ffdh.scalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .rax).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

theorem AttemptPost.keep {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State}
    (h : AttemptPost p rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32) : AttemptPost p rand used t := by
  unfold AttemptPost at h ⊢
  rw [hm, hr]
  exact h

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocated 40 s).wr) : Covers (callWrites p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  have hi := h.input
  obtain ⟨-, -, -, hwr, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := hi.1
  rw [h.wr, hwr]
  cases hi.2
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [inWrites, inX, keyOfState, hrsi]
  · simp [inWrites, inY, keyOfState, hrcx]
  · simp [inWrites, inScr, keyOfState]

theorem call_covers_reads (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    {u : State} (hrd : u.rd = (allocated 40 s).rd) (hw : u.wr = (allocated 40 s).wr) :
    Covers (callReads p used ++ callWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  intro r hr
  simp only [callReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨inDom original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inDom original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 40, 40⟩, ?_, 0, ?_, Nat.le_refl _⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [h.rsp, BitVec.add_zero]; rfl

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State}
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 40) {d : Nat} (hd : d ≤ 8)
    (hf : Frame (callWrites p ++ [below (u.gpr .rsp) (d + 8)]) u.mem t.mem) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := hi.1
  have hsp : s.gpr .rsp = original.gpr .rsp := by rw [h.rsp, ← hi.2]; rfl
  have h1 : Frame (KeyInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p used) (size := 40) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below (original.gpr .rsp) stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [hsp]
    exact Offset.sub_below _ (by decide) (by decide)
  have h2 : Frame (KeyInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · cases hi.2
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨inX original, by simp [KeyInput.callChanges], by
          simp only [inX, keyOfState, hrsi]; exact fun _ hi => hi⟩
      · exact ⟨inY original, by simp [KeyInput.callChanges], by
          simp only [inY, keyOfState, hrcx]; exact fun _ hi => hi⟩
      · exact ⟨inScr original, by simp [KeyInput.callChanges], fun _ hi => hi⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨below (original.gpr .rsp) stackUse, by simp [KeyInput.callChanges], ?_⟩
      rw [hu, ← hsp, h.rsp]
      show Region.Sub ⟨p.sp - 40 - BitVec.ofNat 64 (d + 8), d + 8⟩ ⟨p.sp - BitVec.ofNat 64 56, 56⟩
      rw [BitVec.sub_sub, show (40 : BitVec 64) + BitVec.ofNat 64 (d + 8) = BitVec.ofNat 64 (48 + d) by
        rw [show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl, ← BitVec.ofNat_add]; congr 1; omega]
      exact Offset.sub_below _ (by omega) (by omega)
  exact h1.trans h2

/-- What the call's entry changes: the arguments and its return address. -/
theorem call_mem_frame (h : KeyLive p original used keys scalars s) {u : State}
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 40) : Frame (KeyInput.changes original) s.mem (callState p used u).mem := by
  have hi := h.input
  have hsp : s.gpr .rsp = original.gpr .rsp := by rw [h.rsp, ← hi.2]; rfl
  have hb : Region.Sub (below (original.gpr .rsp) stackUse) (below (original.gpr .rsp) stackUse) :=
    fun _ h => h
  have hin : below (original.gpr .rsp) stackUse ∈ KeyInput.changes original := by
    simp [KeyInput.changes]
  have h1 : Frame (KeyInput.changes original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p used) (size := 40) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, hin, ?_⟩
    rw [hsp]
    exact Offset.sub_below _ (by decide) (by decide)
  refine h1.trans ?_
  simp only [State.withRegions_mem, State.callEntry_mem]
  refine Frame.writeW (Frame.refl _ _) hin _ ?_
  rw [hu, ← h.rsp, hsp]
  have he : original.gpr .rsp - 40 - 8 = original.gpr .rsp - BitVec.ofNat 64 48 := by
    rw [BitVec.sub_sub]; rfl
  rw [he, show original.gpr .rsp - BitVec.ofNat 64 48 =
      original.gpr .rsp - BitVec.ofNat 64 56 + BitVec.ofNat 64 8 from Offset.sub_ofNat_eq _ (by decide)]
  exact Offset.contains_base _ (by decide) (by decide)

end

end VG.Proof.Ffdh.X86_64.KeyGeneration
