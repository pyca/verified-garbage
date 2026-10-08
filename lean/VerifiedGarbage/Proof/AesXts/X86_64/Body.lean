import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.AesXts.Batch
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# XTS-AES on x86-64: all the blocks in one call

`batch_wp`: from AES-CBC's loop invariant after no blocks
(`Proof/AesCbc/X86_64/Loop.lean`), `batch` reaches it after all of them, for
`xtsMode enc`, for any implementation of the block functions (`BlocksImpl`).
The tweak is saved (`saveT_wp`); a pass XORs each block's tweak into it,
multiplying the tweak by `α` after each (`pass_wp`, by `pstep_wp` for one
block, whose invariant `PInv` says what `xored` the blocks are); the tweak is
restored and the block function called on all the blocks (`callArgs_wp`,
`call_wp`, from AES-OCB's `BCall`); and a second pass XORs the tweaks in
again (`AesXts.crypt_eq`).
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore xorInto copy cOff advance)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state
  aesInvWith_state Mode ciphOf length_blocksAt getElem_blocksAt bytesAt_toList)
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesXts (xored xored_zero xored_getElem xored_step xored_all crypt_eq)

/-- The saved copy of the tweak. -/
abbrev Sv (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 2048

/-- A pass over the blocks `ys`, after `i` of them, with `r10` and `r11`
kept. -/
structure PInv (s₀ : State) (ys : List (List Byte)) (x10 x11 : BitVec 64) (i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ i
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - i)
  r15 : s.gpr .r15 = S s₀
  r10 : s.gpr .r10 = x10
  r11 : s.gpr .r11 = x11
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = xored (iv0 s₀) ys i
  iv : bytesAt s.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) i
  sv : bytesAt s.mem (Sv s₀) 16 = iv0 s₀

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

theorem length_xored (t : List Byte) (ys : List (List Byte)) (i : Nat) (hi : i ≤ ys.length) :
    (xored t ys i).length = ys.length := by
  simp [xored, AesXts.length_tweaks]; omega

/-- The blocks after a frame outside them. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ j < n, ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  simp only [Spec.Cbc.blocksAt]
  exact List.map_congr_left fun j hj => bytesAt_frame hf (hd j (List.mem_range.mp hj)) (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dataBlk {j : Nat} (hj : j < N s₀) {r : Region} (hr : (dataR s₀).Disjoint r) :
    (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
  hr.sub_left (UPre.data_sub hj)

/-- One block of a pass. -/
theorem pstep_wp {ys : List (List Byte)} {x10 x11 : BitVec 64} {i : Nat} (hi : i < N s₀) {s : State}
    (h : PInv s₀ ys x10 x11 i s) :
    WP isa (.block passBody) s fun s' =>
      PInv s₀ ys x10 x11 (i + 1) s' ∧ s'.zf = some (decide (N s₀ - (i + 1) = 0)) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ i) (Q := Iv s₀) h.r13 h.r12
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hi))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hi))
  have hR₁ : s₁.rd ++ s₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₁, wr₁, hR]
  have hW₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, hW]
  obtain ⟨s₂, run₂, g₂, mem₂, rd₂, wr₂⟩ :=
    mulA_ok s₁ (Q := Iv s₀) (by rw [g₁ _ (by decide), h.r12])
      (by rw [hR₁]; exact in_rw (by simp) cIv0) (by rw [hR₁]; exact in_rw (by simp) cIv8)
      (by rw [hW₁]; exact in_rw (by simp) cIv0) (by rw [hW₁]; exact in_rw (by simp) cIv8)
  obtain ⟨s₃, run₃, r13₃, r14₃, zf₃, keep₃, mem₃, rd₃, wr₃⟩ := advance_regs (s := s₂) hi
    (by rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r13])
    (by rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r14])
  rw [passBody, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, WP.of_runBlock ⟨s₃, run₃, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .rdx) (h13 : r ≠ .r13) (h14 : r ≠ .r14) :
      s₃.gpr r = s.gpr r := by
    rw [keep₃ r h13 h14, g₂ r h1 h2 h3, g₁ r h1]
  have f₁ : Frame [⟨blk s₀ i, 16⟩] s.mem s₁.mem := by rw [mem₁]; exact xorMem_frame _ _ _
  have f₂ : Frame [ivR s₀] s₁.mem s₂.mem := by rw [mem₂]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ i, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₃.mem := by
    rw [mem₃]
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have hy : i < ys.length := by rw [h.len]; exact hi
  have blkI : bytesAt s.mem (blk s₀ i) 16 = ys[i] := by
    have := congrArg (·[i]?) h.data
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi),
      getElem_blocksAt _ _ hi, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  have newBlk : bytesAt s₃.mem (blk s₀ i) 16 = Spec.Cbc.xor ys[i] (Spec.Xts.next (iv0 s₀) i) := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one (hp.blk_iv hi)) (by decide), mem₁,
      xorMem_bytes _ (hp.blk_iv hi), blkI, h.iv]
  have newIv : bytesAt s₃.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (i + 1) := by
    rw [mem₃, mem₂, alphaMem_bytes, mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hi).symm) (by decide), h.iv]
    rfl
  have newSv : bytesAt s₃.mem (Sv s₀) 16 = iv0 s₀ := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one hp.iv_sv.symm) (by decide), mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_sv hi).symm) (by decide), h.sv]
  refine ⟨⟨?_, ?_, ?_, r13₃, r14₃, ?_, ?_, ?_, ?_, ?_, ?_, h.frame.trans (stepFrame hi fStep), h.len,
    ?_, newIv, newSv⟩, zf₃⟩
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide) (by decide) (by decide), h.r12]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h.r15]
  · rw [g .r10 (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by decide) (by decide) (by decide) (by decide) (by decide), h.r11]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), h.rsp]
  · rw [rd₃, rd₂, rd₁, h.rd]
  · rw [wr₃, wr₂, wr₁, h.wr]
  · rw [hp.blocksAt_step hi fStep, h.data, newBlk, xored_step _ hy]

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} {x10 x11 : BitVec 64} (hN : 0 < N s₀) {s : State}
    (h : PInv s₀ ys x10 x11 0 s) : WP isa pass s (PInv s₀ ys x10 x11 (N s₀)) := by
  refine WP.loop (M := isa) (body := .block passBody) (c := .ne) (Q := PInv s₀ ys x10 x11 (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ PInv s₀ ys x10 x11 j t) ?_ (N s₀ - 0) s
    ⟨0, rfl, hN, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (pstep_wp hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

omit hp in
theorem movs_ok (s : State) :
    ∃ s', runBlock isa [.mov .r10 (.reg .r13), .mov .r11 (.reg .r14)] s = some s' ∧
      s'.gpr .r10 = s.gpr .r13 ∧ s'.gpr .r11 = s.gpr .r14 ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-- The tweak saved, and the data pointer and number of blocks kept. -/
theorem saveT_wp {M : Mode} (hM : ∀ R w t, M.chain R w t [] = t) (hO : ∀ R w t, M.out R w t [] = [])
    {s : State} (h : LInv M s₀ 0 s) :
    WP isa (.block saveT) s (PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .r15) (src := .r12) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.r15]; rfl) (by rw [h.r15, Offset.add_add]; rfl) (by simp [h.r12])
      (by simp [h.r12]) (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8) (by decide) (by decide)
  obtain ⟨s₂, run₂, r10₂, r11₂, g₂, mem₂, rd₂, wr₂⟩ := movs_ok s₁
  rw [saveT, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .r10) (h3 : r ≠ .r11) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h2 h3, g₁ r h1]
  have fC : Frame [⟨Sv s₀, 16⟩] s.mem s₂.mem := by rw [mem₂, mem₁]; exact copyMem_frame _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [Spec.Cbc.blocksAt], ?_, ?_, ?_⟩
  · rw [g .rbx (by decide) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide), h.r12]
  · rw [g .r13 (by decide) (by decide) (by decide), h.r13]
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [r10₂, g₁ _ (by decide), h.r13]
  · rw [r11₂, g₁ _ (by decide), h.r14]; rfl
  · rw [g .rsp (by decide) (by decide) (by decide), h.rsp]
  · rw [rd₂, rd₁, h.rd]
  · rw [wr₂, wr₁, h.wr]
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (UPre.dataBlk hj hp.data_scr).sub_right (UPre.scr_sub (by decide))), h.data, xored_zero]
    simp [outK, hO]
  · rw [bytesAt_frame fC (one hp.iv_sv) (by decide), h.iv]; simp [chainK, hM]; rfl
  · rw [mem₂, mem₁, copyMem_bytes _ hp.iv_sv.symm, h.iv]; simp [chainK, hM]

omit hp in
theorem movsBack_ok (s : State) :
    ∃ s', runBlock isa [.mov .r13 (.reg .r10), .mov .r14 (.reg .r11)] s = some s' ∧
      s'.gpr .r13 = s.gpr .r10 ∧ s'.gpr .r14 = s.gpr .r11 ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

omit hp in
theorem args_ok (s : State) :
    ∃ s', runBlock isa [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r13),
        .mov .rcx (.reg .r14), .mov .r8 (.reg .r15)] s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r13 ∧
      s'.gpr .rcx = s.gpr .r14 ∧ s'.gpr .r8 = s.gpr .r15 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩

/-- The arguments of the block function on all the blocks. -/
theorem UPre.bcall {s : State} (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi)
    (rdx : s.gpr .rdx = Dp s₀) (rcx : s.gpr .rcx = BitVec.ofNat 64 (N s₀)) (r8 : s.gpr .r8 = S s₀)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Proof.AesOcb.X86_64.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wrap := hp.data_wrap
  kd := hp.sch_data
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.data_scr.sub_right (Region.sub_prefix (by decide))
  stkK := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_data
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The data pointer and number of blocks back, the tweak restored, and the
arguments of the block function. -/
theorem callArgs_wp {ys : List (List Byte)} {s : State}
    (h : PInv s₀ ys (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) (N s₀) s) :
    WP isa (.block callArgs) s fun s' =>
      Proof.AesOcb.X86_64.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) ys (N s₀)) (s'.gpr .r10) (s'.gpr .r11) 0 s' := by
  obtain ⟨s₁, run₁, r13₁, r14₁, g₁, mem₁, rd₁, wr₁⟩ := movsBack_ok s
  have hR₁ : s₁.rd ++ s₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₁, wr₁, h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, h.wr, hp.wr]
  have r12₁ : s₁.gpr .r12 = Iv s₀ := by rw [g₁ _ (by decide) (by decide), h.r12]
  have r15₁ : s₁.gpr .r15 = S s₀ := by rw [g₁ _ (by decide) (by decide), h.r15]
  obtain ⟨s₂, run₂, g₂, mem₂, rd₂, wr₂⟩ :=
    copy_ok s₁ (dst := .r12) (src := .r15) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
      (by simp [r12₁]) (by simp [r12₁]) (by rw [r15₁]; rfl) (by rw [r15₁, Offset.add_add]; rfl)
      (by rw [hR₁]; exact in_rw (by simp) cSv0) (by rw [hR₁]; exact in_rw (by simp) cSv8)
      (by rw [hW₁]; exact in_rw (by simp) cIv0) (by rw [hW₁]; exact in_rw (by simp) cIv8) (by decide) (by decide)
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, g₃, mem₃, rd₃, wr₃⟩ := args_ok s₂
  rw [callArgs, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, WP.of_runBlock ⟨s₃, run₃, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rdi) (h2 : r ≠ .rsi) (h3 : r ≠ .rdx) (h4 : r ≠ .rcx) (h5 : r ≠ .r8)
      (h6 : r ≠ .rax) (h7 : r ≠ .r13) (h8 : r ≠ .r14) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h1 h2 h3 h4 h5, g₂ r h6, g₁ r h7 h8]
  have r13₃ : s₃.gpr .r13 = blk s₀ 0 := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), r13₁, h.r10]
  have r14₃ : s₃.gpr .r14 = BitVec.ofNat 64 (N s₀) := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), r14₁, h.r11]
  have fC : Frame [ivR s₀] s.mem s₃.mem := by rw [mem₃, mem₂, mem₁]; exact copyMem_frame _ _ _
  have hrsp : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.rsp]
  have hrd : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁, h.rd]
  have hwr : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, h.wr]
  have hlen : ys.length = N s₀ := h.len
  refine ⟨UPre.bcall hp
    (by rw [rdi₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), h.rbx])
    (by rw [rsi₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), h.rbp])
    (by rw [rdx₃, g₂ _ (by decide), r13₁, h.r10]; simp [blk])
    (by rw [rcx₃, g₂ _ (by decide), r14₁, h.r11])
    (by rw [r8₃, g₂ _ (by decide), r15₁]) hrsp hrd hwr, ?_⟩
  refine ⟨?_, ?_, ?_, r13₃, by rw [r14₃]; rfl, ?_, rfl, rfl, hrsp, hrd, hwr, ?_,
    by rw [length_xored _ _ _ (by omega), hlen], ?_, ?_, ?_⟩
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.r12]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.r15]
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact UPre.dataBlk hj hp.iv_data.symm), h.data, xored_zero]
  · rw [mem₃, mem₂, copyMem_bytes _ hp.iv_sv, mem₁, h.sv]; rfl
  · rw [bytesAt_frame fC (one hp.iv_sv.symm) (by decide), h.sv]

omit hp in
/-- The blocks after a call of a block function on all of them. -/
theorem blocksAt_of_out {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    {c : List Byte → List Byte} (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g)
    (hc : ∀ p, (g (Spec.Aes.stateAt m p)).toList = c (bytesAt m p 16)) :
    Spec.Cbc.blocksAt m' D n = (Spec.Cbc.blocksAt m D n).map c := by
  simp only [Spec.Cbc.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp]
  rw [bytesAt_toList, Proof.AesOcb.X86_64.stateAt_of_statesAt h (List.mem_range.mp hj), hc]

/-- The call of the block function on all the blocks. -/
theorem call_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {ys : List (List Byte)} {x10 x11 : BitVec 64} {s : State}
    (hc : Proof.AesOcb.X86_64.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀)) (h : PInv s₀ ys x10 x11 0 s) :
    WP isa (.call b.name b.code) s fun s' =>
      PInv s₀ (ys.map (ciphOf enc (R s₀) (wK s₀))) (s'.gpr .r10) (s'.gpr .r11) 0 s' := by
  refine WP.mono (Proof.AesOcb.X86_64.blk_call ok nosp depth hc) fun s' c => ?_
  have g (r : Reg) (hr : r ∈ calleeSaved) : s'.gpr r = s.gpr r := c.saved r hr
  have hrsp := h.rsp
  have fCall : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s'.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [hrsp]; exact fun _ h => h⟩
  have dIv : ∀ r ∈ [(⟨Dp s₀, 16 * N s₀⟩ : Region), ⟨S s₀, 2048⟩, below (s.gpr .rsp) 8],
      (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_data
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · rw [hrsp]; exact hp.stk_iv.symm
  have dSv : ∀ r ∈ [(⟨Dp s₀, 16 * N s₀⟩ : Region), ⟨S s₀, 2048⟩, below (s.gpr .rsp) 8],
      (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_right (UPre.scr_sub (by decide))).symm
    · exact hp.sv_scr
    · rw [hrsp]; exact (hp.stk_scr.sub_right (UPre.scr_sub (by decide))).symm
  have sched : bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp (UPre.big_of h.frame)
  refine ⟨by rw [g .rbx (by simp [calleeSaved]), h.rbx], by rw [g .rbp (by simp [calleeSaved]), h.rbp],
    by rw [g .r12 (by simp [calleeSaved]), h.r12], by rw [g .r13 (by simp [calleeSaved]), h.r13],
    by rw [g .r14 (by simp [calleeSaved]), h.r14], by rw [g .r15 (by simp [calleeSaved]), h.r15], rfl, rfl,
    by rw [g .rsp (by simp [calleeSaved]), h.rsp], by rw [c.rd, h.rd], by rw [c.wr, h.wr],
    h.frame.trans fCall, by simp [h.len], ?_, ?_, ?_⟩
  · rw [blocksAt_of_out c.out (fun p => hf _ _ _ p), h.data, xored_zero, xored_zero, sched]
  · rw [bytesAt_frame c.frame dIv (by decide), h.iv]
  · rw [bytesAt_frame c.frame dSv (by decide), h.sv]

omit hp in
/-- After the second pass: XTS of all the blocks (`AesXts.crypt_eq`). -/
theorem final_of (enc : Bool) {x10 x11 : BitVec 64} {s : State}
    (h : PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) x10 x11 (N s₀) s) :
    LInv (AesXts.xtsMode enc) s₀ (N s₀) s := by
  have hl : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  have ce := crypt_eq (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)
  rw [hl] at ce
  exact { rbx := h.rbx, rbp := h.rbp, r12 := h.r12, r13 := h.r13, r14 := h.r14, r15 := h.r15,
          rsp := h.rsp, rd := h.rd, wr := h.wr, frame := h.frame
          data := by
            rw [h.data, xored_all _ h.len, xored_all _ hl, ce, outK, AesXts.xtsMode_out,
              List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]
          iv := by
            rw [h.iv, chainK, AesXts.xtsMode_chain, List.take_of_length_le (by omega), hl] }

/-- All the blocks. -/
theorem batch_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hN : 0 < N s₀) {s : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s) :
    WP isa (batch b) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h) fun _ h₁ =>
    WP.seq (WP.mono (pass_wp hp hN h₁) fun _ h₂ =>
      WP.seq (WP.mono (callArgs_wp hp h₂) fun _ ⟨c₃, h₃⟩ =>
        WP.seq (WP.mono (call_wp hp enc ok nosp depth hf c₃ h₃) fun _ h₄ =>
          WP.mono (pass_wp hp hN h₄) fun _ h₅ => final_of enc h₅))))

end

/-- The whole function. -/
theorem crypt_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt b) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => batch_wp hp enc ok nosp depth hf hN h

end VG.Proof.AesXts.X86_64
