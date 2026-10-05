import VerifiedGarbage.Proof.AesOcb.Arm.Env
import VerifiedGarbage.Proof.Aes.Arm.Blocks

/-!
# AES-OCB on ARMv7: the functions called

Untrusted: everything here is checked by Lean. A call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (`BlkFn`), from its
callee's contract (with `WP.call`), with the regions it is given: what it
needs (`BlkCall`) and what it leaves (`BlkPost`); and that it is constant
time (`blk_rel`). They are called in a frame that pushes their stack argument
(`push {r12, lr}`) in the 8 bytes below the stack pointer, as `vg_ghash` is
(`Proof.AesGcm.Arm.gh_call`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (below toNat_ofNat32 pushed_sp8 hspA fA popSlot view_gpr view_sp view_mem arg0
  argAddr0 cover_pushed cover_pushed' cover_frame covers_append' bytesAt_frame)

/-- A function on whole blocks that OCB calls: its name and code, what it
does to each block, and that it is verified. -/
structure BlkFn where
  name : String
  code : Prog isa
  f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State
  correct : ∀ s, (Proof.Aes.blocksArm f).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksArm f).post s s'
  ct : ConstantTime isa (Proof.Aes.blocksArm f).pre (Proof.Aes.blocksArm f).pub code
  noCalls : code.noCalls = true

theorem statesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Aes.statesAt m' p n = Spec.Aes.statesAt m p n := by
  simp only [Spec.Aes.statesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simp only [Spec.Aes.stateAt]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  rw [Offset.add_add]
  exact hf.bytes (R := ⟨p, 16 * n⟩) hd hn (show 16 * i + j < 16 * n by omega)

theorem enc_noCalls : Impl.Aes.Arm.encryptBlocks.noCalls = true := by decide +kernel
theorem dec_noCalls : Impl.Aes.Arm.decryptBlocks.noCalls = true := by decide +kernel

/-- `vg_aes_encrypt_blocks`. -/
def encF : BlkFn where
  name := "vg_aes_encrypt_blocks"
  code := Impl.Aes.Arm.encryptBlocks
  f := Spec.Aes.cipher
  correct := Proof.Aes.Arm.Ecb.blocks_correct Proof.Aes.Arm.Ecb.encrypt2_cryptOk
  ct := Proof.Aes.Arm.Ecb.encryptBlocks_ct
  noCalls := enc_noCalls

/-- `vg_aes_decrypt_blocks`. -/
def decF : BlkFn where
  name := "vg_aes_decrypt_blocks"
  code := Impl.Aes.Arm.decryptBlocks
  f := Spec.Aes.invCipher
  correct := Proof.Aes.Arm.Ecb.blocks_correct Proof.Aes.Arm.Ecb.decrypt2_cryptOk
  ct := Proof.Aes.Arm.Ecb.decryptBlocks_ct
  noCalls := dec_noCalls

/-- The call of `F` in its frame. -/
def blkFrame (F : BlkFn) : Prog isa := .frame (.push [.r12, .lr]) (.call F.name F.code) (.pop .r12 8)

theorem encFrame_eq : Impl.AesOcb.Arm.encFrame = blkFrame encF := rfl
theorem decFrame_eq : Impl.AesOcb.Arm.decFrame = blkFrame decF := rfl

/-- What a call of a `BlkFn` needs: the key schedule at `K` for `R` rounds,
`n` blocks at `D` and working space at `S`, in `r12` to push. -/
structure BlkCall (s : State) (K D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r12 : s.gpr .r12 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  kd : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bk : (below s.sp).Disjoint ⟨State.addr K, 240⟩
  bd : (below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (below s.sp).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩] s.wr

/-- What a call of `F` leaves. -/
structure BlkPost (F : BlkFn) (s : State) (K D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩, below s.sp] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (State.addr D) n =
    (Spec.Aes.statesAt s.mem (State.addr D) n).map
      (F.f R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1))))

abbrev blkRd (sp K : BitVec 32) : List Region := [⟨State.addr K, 240⟩, ⟨State.addr sp - 8, 4⟩]
abbrev blkWr (D S : BitVec 32) (n : Nat) : List Region := [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩]

namespace BlkCall
variable {s : State} {K D S : BitVec 32} {R n : Nat} (h : BlkCall s K D S R n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem toNat_R : (BitVec.ofNat 32 R).toNat = R := toNat_ofNat32 (by rcases h.rounds with h' | h' | h' <;> omega)

theorem pre (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : (Proof.Aes.blocksArm f).pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (blkRd s.sp K) (blkWr D S n)) := by
  have hn := toNat_ofNat32 h.n_lt
  have b4 : ∀ x : Region, (below s.sp).Disjoint x → (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint x :=
    fun x hx => hx.sub_left (Region.sub_prefix (by decide))
  simp only [Proof.Aes.blocksArm, arg0 h.hsp, argAddr0 h.hsp, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, hn, h.toNat_R, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, view_sp, hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions,
    Proof.AesGcm.Arm.stackArg_callEntry, Proof.AesGcm.Arm.stackArgAddr_callEntry, arg0 h.hsp, argAddr0 h.hsp, h.r12]
  refine ⟨trivial, trivial, h.kd, h.ks, h.ds, (b4 _ h.bd).symm, (b4 _ h.bs).symm, h.fitK, h.fitD, h.fitS, ?_,
    h.rounds⟩
  have := s.sp.isLt; omega

theorem cov : Covers (blkRd s.sp K ++ blkWr D S n)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have e : blkRd s.sp K = [⟨State.addr K, 240⟩] ++ [⟨State.addr s.sp - 8, 4⟩] := rfl
  rw [e]
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (blkWr D S n) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end BlkCall

theorem blk_call (F : BlkFn) {s : State} {K D S : BitVec 32} {R n : Nat} (h : BlkCall s K D S R n) :
    WP isa (blkFrame F) s (BlkPost F s K D S R n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.blocksArm F.f) F.correct
    (rd := blkRd s.sp K) (wr := blkWr D S n) (h.pre F.f) h.cov h.covW ?_ F.noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have fA' := fA (s := s) h.hsp
  have bytesK : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) (16 * (R + 1)) =
      Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)) :=
    bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.symm.sub_left (Region.sub_prefix hR'))) (by omega)
  have statesD : Spec.Aes.statesAt (pushed [.r12, .lr] s).mem (State.addr D) n =
      Spec.Aes.statesAt s.mem (State.addr D) n :=
    statesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  simp only [Proof.Aes.blocksArm, State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hn, h.toNat_R, bytesK, statesD] at hpost
  have fB : Frame (blkWr D S n) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem blk_rel (F : BlkFn) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : BitVec 32, ∃ R n : Nat,
      BlkCall s₁ K D S R n ∧ BlkCall s₂ K D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (blkFrame F) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Aes.blocksArm F.f) F.correct F.ct
    (blkRd s₁.sp K) (blkWr D S n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre F.f
  have p₂ := h₂.pre F.f
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Aes.blocksArm, stackArg_withRegions, Proof.AesGcm.Arm.stackArg_callEntry, arg0 h₁.hsp,
    arg0 h₂.hsp, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.Arm
