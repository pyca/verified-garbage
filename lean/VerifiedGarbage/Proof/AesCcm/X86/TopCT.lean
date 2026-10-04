import VerifiedGarbage.Proof.AesCcm.X86.Top
import VerifiedGarbage.Proof.AesCcm.X86.Seal
import VerifiedGarbage.Proof.AesCcm.X86.MacCT
import VerifiedGarbage.Proof.AesCcm.X86.CryptCT

/-!
# AES-CCM on x86: the start, and what the pieces after it keep, for
constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public (`pubOf`); from them, `seal` and `open` start (`Top`), the entry and
`Ctr₀` are constant time (`start_ct`), and after them each piece keeps `Run`,
from which the next one's precondition follows.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains ofNat_toNat32 length_bytesAt)

/-- What is public: `esp` and the arguments. -/
def pubOf (s : State) : BitVec 32 × (Nat → BitVec 32) := (s.gpr .esp, fun i => if i < 10 then arg s i else 0)

theorem pubOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : pubOf s₁ = pubOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

/-- `seal` and `open` from their arguments. -/
structure Top (K W SP N A D : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  args : Args s K W SP N A D R nl al n tl
  sp : s.gpr .esp = SP
  a0 : arg s 0 = K
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = N
  a3 : arg s 3 = BitVec.ofNat 32 nl
  a4 : arg s 4 = A
  a5 : arg s 5 = BitVec.ofNat 32 al
  a6 : arg s 6 = D
  a7 : arg s 7 = BitVec.ofNat 32 n
  a8 : arg s 8 = W
  a9 : arg s 9 = BitVec.ofNat 32 tl

/-- `Top` for the public values `p`. -/
abbrev TopOf (p : BitVec 32 × (Nat → BitVec 32)) : State → Prop :=
  Top (p.2 0) (p.2 8) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat (p.2 7).toNat
    (p.2 9).toNat

theorem top_of {s : State} (h : onePre s) {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) : TopOf p s := by
  subst hp
  simp only [pubOf, show (0 : Nat) < 10 from by decide, show (1 : Nat) < 10 from by decide,
    show (2 : Nat) < 10 from by decide, show (3 : Nat) < 10 from by decide, show (4 : Nat) < 10 from by decide,
    show (5 : Nat) < 10 from by decide, show (6 : Nat) < 10 from by decide, show (7 : Nat) < 10 from by decide,
    show (8 : Nat) < 10 from by decide, show (9 : Nat) < 10 from by decide, ↓reduceIte]
  exact ⟨args_of h, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩

/-! ## The start -/

theorem entry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 8 = W ∧ Covers [argsR SP 10] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 10 ≤ 2 ^ 32) : CT I ccmEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem start_ct {K W SP N A D : BitVec 32} {R nl al n tl : Nat} (L : Lay K W SP) (h13 : nl ≤ 13) :
    CT (Top K W SP N A D R nl al n tl) (.seq ccmEntry ctrs) := by
  refine CT.seq (J := fun s₁ => ∃ s, Top K W SP N A D R nl al n tl s ∧ Entered s W s₁)
    (entry_ct fun s hs => ⟨hs.sp, hs.a8, hs.args.args, hs.args.fa⟩)
    (fun s hs => WP.mono (entry_ok hs.a8 hs.args.perm.w (by rw [hs.sp]; exact hs.args.args)
      (by rw [hs.sp]; exact hs.args.argsW) (by rw [hs.sp]; exact hs.args.fa) L.fw) fun s₁ E => ⟨s, hs, E⟩)
    (ctrs_ct L h13 fun s₁ ⟨s, hs, E₀⟩ => ⟨⟨E₀.ebp, by rw [E₀.esp, hs.sp], hs.args.perm.of_eq E₀.rd E₀.wr⟩,
      by rw [E₀.slots (2, nonceO) (by simp), hs.a2], by rw [E₀.slots (3, nlenO) (by simp), hs.a3]⟩)

/-! ## What the pieces keep -/

/-- After the start, and the pieces after it. -/
structure Run (s₀ : State) (K W SP N A D : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : ∃ s₂, Started s₀ K W SP N A D R nl al n tl s₂ ∧ Frame (mutR W SP D n) s₂.mem s.mem
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s₀.mem (w64 N) nl) 0

section
variable {s₀ : State} {K W SP N A D : BitVec 32} {R nl al n tl : Nat}

theorem Run.of_started {s₂ : State} (St : Started s₀ K W SP N A D R nl al n tl s₂) :
    Run s₀ K W SP N A D R nl al n tl s₂ :=
  ⟨St.env, St.rd, St.wr, ⟨s₂, St, Frame.refl _ _⟩, St.c0⟩

theorem Run.step {s : State} (h : Run s₀ K W SP N A D R nl al n tl s) {s' : State} (E : Env K W SP s')
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) {rs : List Region} (f : Frame rs s.mem s'.mem) (hm : InMut W SP D n rs)
    (hc : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) : Run s₀ K W SP N A D R nl al n tl s' := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨s₂, St, f₂.trans (frame_toMut f hm)⟩,
    by rw [Proof.AesGcm.X86.bytesAt_frame f hc (by decide), h.c0]⟩

theorem Run.slots {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s) :
    Slots W K R N A D nl al n tl s.mem := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact (St.mut Ar f₂).1

theorem Run.mac_pre {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s) :
    MacPre K W SP R N A D nl al n tl s :=
  ⟨⟨h.env, h.slots Ar, Ar.aad.of_eq h.rd h.wr, Ar.data.of_eq h.rd h.wr⟩,
    ⟨_, length_bytesAt _ _ _, h.c0⟩⟩

theorem Run.tag_pre {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s) :
    TagPre K W SP R s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds,
    ⟨_, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13, h.c0⟩⟩

theorem Run.ctr_pre {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s) :
    CtrPre K W SP R D n s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds, (h.slots Ar).data, (h.slots Ar).len,
    ⟨_, ⟨Ar.lay, Ar.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, Ar.n32, h.c0, Ar.data.of_eq h.rd h.wr, by rw [h.wr]; exact Ar.dw,
      Ar.dk⟩⟩⟩

/-- After the MAC into `W + y`. -/
theorem Run.mac {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Y : List Byte} {s' : State} (A' : Absorbed K W SP s y Y s') :
    Run s₀ K W SP N A D R nl al n tl s' :=
  h.step A'.env A'.rd A'.wr A'.frame (inMut_macR W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After the tag at `W + y`. -/
theorem Run.tag {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 56] s.mem s'.mem) :
    Run s₀ K W SP N A D R nl al n tl s' :=
  h.step E rd wr f (inMut_tag W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After counter mode. -/
theorem Run.ctr {s : State} (Ar : Args s₀ K W SP N A D R nl al n tl) (h : Run s₀ K W SP N A D R nl al n tl s)
    {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (f : Frame (ctrR W SP D n) s.mem s'.mem) :
    Run s₀ K W SP N A D R nl al n tl s' :=
  h.step E rd wr f (inMut_ctrR W SP D n) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm
    · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm

end

end VG.Proof.AesCcm.X86
