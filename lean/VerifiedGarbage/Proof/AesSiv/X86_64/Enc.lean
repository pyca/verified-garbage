import VerifiedGarbage.Proof.AesSiv.X86_64.Open
import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV on x86-64: `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

Both save the registers in the working space and keep the arguments in them
and in its slots (`encPre_ok`), start S2V into `D = W + 2560` with the CMAC
of the zero block (`start_wp`), absorb the components of associated data,
one per iteration (`ads_wp`), and then go on as `sealTail_wp` and
`openTail_wp` say from S2V's state. `encrypt` then copies the IV from the
working space to `siv` (`sivOut_ok`), whose address and the working space's
are still on the stack (`SivArg`); `decrypt` copies the received IV from
`siv` to the working space after S2V of the associated data (`sivIn_wp`).

The proofs are on the state whose writable regions are the data, `siv` for
`encrypt`, the first 2560 bytes of the working space and `D` (`EPre`);
`Verified.lean` moves them to the shared contracts with the working space as
an argument, one region of 2576 bytes.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What `encrypt` and `decrypt` need of their arguments, on the state with
narrowed permissions: the key context `C`, the rounds `R`, the `N`
descriptors at `A`, the data `P` (`L` bytes), the working space `W`, whose
address is the stack argument, and S2V's state `D` after its first 2560
bytes. Each component a descriptor lists is a message as the data is
(`comps`). -/
structure EPre (s₀ : State) (C A P W D : Addr) (R N L : Nat) : Prop where
  env : Env s₀ C D P W R L
  hD : D = W + BitVec.ofNat 64 dOff
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  dw : (⟨D, 16⟩ : Region) ∈ s₀.wr
  rdi : s₀.gpr .rdi = C
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 R
  rdx : s₀.gpr .rdx = A
  rcx : s₀.gpr .rcx = BitVec.ofNat 64 N
  r8 : s₀.gpr .r8 = P
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 L
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 16) 8
  descIn : (⟨A, N * 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  desc_w : (⟨A, N * 16⟩ : Region).Disjoint ⟨W, 2560⟩
  desc_d : (⟨A, N * 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_desc : (below (s₀.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩
  wA : A.toNat + N * 16 ≤ 2 ^ 64
  comps : ∀ r ∈ Sig.listed 64 s₀.mem .u8 A N, Env s₀ C D r.base W R r.len

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat}

/-! ## The save -/

/-- The memory after saving the registers and the arguments in the slots. -/
def encMem (s₀ : State) (A P W : Addr) (N L : Nat) : Mem :=
  ((((Spill.saveMem s₀.mem W s₀.gpr saved).writeW (W + BitVec.ofNat 64 dataOff) P).writeW
    (W + BitVec.ofNat 64 lenOff) (BitVec.ofNat 64 L)).writeW (W + BitVec.ofNat 64 adsOff) A).writeW
    (W + BitVec.ofNat 64 leftOff) (BitVec.ofNat 64 N)

theorem encPre_ok (h : EPre s₀ C A P W D R N L) :
    ∃ s₁, runBlock isa encPre s₀ = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧ s₁.gpr .rdi = C ∧
      s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = W ∧ s₁.mem = encMem s₀ A P W N L := by
  have e := h.env
  have run₀ : runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s₀ = some (s₀.setReg .rax W) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg]
  have hrun := Spill.save_run .rax saved (s₀.setReg .rax W) (fun p hp => by
    rw [gpr_setReg_self, wr_setReg]; have := saved_le p hp; exact e.inW rfl (by omega))
  rw [gpr_setReg_self, mem_setReg] at hrun
  have w₁ := e.inW (s := s₀) rfl (d := dataOff) (n := 8) (by decide)
  have w₂ := e.inW (s := s₀) rfl (d := lenOff) (n := 8) (by decide)
  have w₃ := e.inW (s := s₀) rfl (d := adsOff) (n := 8) (by decide)
  have w₄ := e.inW (s := s₀) rfl (d := leftOff) (n := 8) (by decide)
  refine ⟨_, by
    rw [encPre, show save .rax = Spill.saveCode .rax saved from rfl, runBlock_append, runBlock_append, run₀,
      Option.bind_some, hrun, Option.bind_some]
    simp only [reduceCtorEq, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu,
      State.store64, State.ea, offset_nat, Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, w₁, w₂, w₃, w₄]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg,
    ite_true, ite_false, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.hD, sx_ofNat (show dOff < 2 ^ 31 by decide)]
  · rfl
  · rfl
  · simp only [reduceCtorEq, encMem, saved, Spill.saveMem, gpr_setReg, ite_false]

/-- The save writes the working space past its first 16 bytes (the IV
`decrypt` is given). -/
theorem encMem_frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩] s₀.mem (encMem s₀ A P W N L) :=
  ((((Spill.saveMem_frame _ _ _ _ (fun p hp => Offset.contains W (by have := saved_ge p hp; omega)
    (by have := saved_le p hp; omega) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))

theorem encMem_saved : Spill.Saved (encMem s₀ A P W N L) W s₀.gpr saved :=
  ((((Spill.saveMem_saved _ _ _ _ saved_slots).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide)
    (by decide) (by decide)).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide) (by decide)
    (by decide)

theorem encMem_slots :
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 adsOff) 64 = A ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 N ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
  have sp {d e : Nat} (hd : d + 8 ≤ e ∨ e + 8 ≤ d) (hd' : d + 8 ≤ 2560) (he : e + 8 ≤ 2560) :
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 e) (64 / 8) :=
    Offset.sep W (n := 8) (k := 8) hd (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [encMem]
  · rw [Mem.readW_writeW_sep (sp (d := adsOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := dataOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := lenOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := lenOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := lenOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]

/-! ## S2V's first state -/

theorem startPre_env (h : EPre s₀ C A P W D R N L) {s : State} (hr : Regs s₀ C D P W R L s)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W) :
    ∃ s', runBlock isa startPre s = some s' ∧ s'.gpr .rcx = W + BitVec.ofNat 64 16 ∧
      s'.gpr .r8 = BitVec.ofNat 64 16 ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 (zero2 s.mem (W + BitVec.ofNat 64 16)) D ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := h.env
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 := by
    rw [hr.wr]; exact ⟨⟨D, 16⟩, h.dw, Offset.contains_base _ hd (by have := e.wD; omega)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, startPre, zero16, zOff, csOff, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu,
      State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, rcx, rdx,
      e.inW hr.wr (d := 16) (n := 8) (by decide), e.inW hr.wr (d := 24) (n := 8) (by decide), inD 0 (by decide),
      inD 8 (by decide)]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    ite_true, ite_false, rcx, sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  · rfl
  · intro r h₁ h₂ h₃ h₄; simp [h₁, h₂, h₃, h₄]
  · simp only [zero2, Offset.add_add, k0]
  all_goals rfl

/-- The arguments of `vg_cmac_aes_finalize` for S2V's first state: the
context as the key, the state `D`, the zero block at `W + 16` and the working
space at `W + 256`. -/
theorem EPre.fargsD (h : EPre s₀ C A P W D R N L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 16) (r8 : s.gpr .r8 = BitVec.ofNat 64 16)
    (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.env.rounds
  len := by decide
  kst := h.c_d.sub_left (Region.sub_prefix (by decide))
  ks := (h.env.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.env.sW (by decide))
  pst := (h.env.d_w.sub_right (h.env.sW (by decide))).symm
  ps := Offset.disjoint W (by omega) (by omega) (by omega)
  sts := h.env.d_w.sub_right (h.env.sW (by decide))
  stkK := by rw [hsp]; exact h.env.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [hsp]; exact h.env.stk_w.sub_right (h.env.sW (by decide))
  stkSt := by rw [hsp]; exact h.env.stk_d
  stkS := by rw [hsp]; exact h.env.stk_w.sub_right (h.env.sW (by decide))
  wrapK := by have := h.env.wC; omega
  wrapSt := h.env.wD
  wrapP := by rw [toNat_add_lt W h.env.wW (by decide)]; have := h.env.wW; omega
  wrapS := by rw [toNat_add_lt W h.env.wW (by decide)]; have := h.env.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_base h.env.ctxIn (by simp))
        (Covers.cons (Covers.right (cov_off h.env.workIn (by simp))) Covers.nil))
      (Covers.cons (Covers.right (cov_base h.dw (by simp)))
        (Covers.cons (Covers.right (cov_off h.env.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_base h.dw (by simp)) (Covers.cons (cov_off h.env.workIn (by simp)) Covers.nil)

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
    Proof.Cmac.bytesAt_length])

/-- The state before the `i`-th component of associated data (and, for
`i = N`, after the last): `D` is S2V's state of the first `i`, the slots at
`W + 112` and `W + 120` hold the next descriptor's address and how many are
left, and the data's, its length's and the registers' slots are as the save
left them. -/
structure AInv (s₀ : State) (C A P W D : Addr) (R N L : Nat) (i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : i ≤ N
  ads : s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = A + BitVec.ofNat 64 (16 * i)
  left : s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i)
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) ((Spec.Siv.components 64 s₀.mem A N).take i)

/-- A slot of the working space outside what S2V's start writes. -/
theorem EPre.start_dis (h : EPre s₀ C A P W D R N L) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 16⟩ : Region), ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩,
      below (s₀.gpr .rsp) 16], Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.env.d_w.sub_right (h.env.sW (by omega))).symm
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.env.stk_w.sub_right (h.env.sW (by omega))).symm

/-- The save, then S2V's first state `D = AES-CMAC(K1, <zero>)` with
`vg_cmac_aes_finalize` of the zero block from a zero state. -/
theorem start_wp (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) :
    WP isa (.block (encPre ++ startPre)) s₀ fun s =>
      FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧ s.gpr .rsp = s₀.gpr .rsp ∧
      WP isa (callFinalize v.callee v.suffix) s (AInv s₀ C A P W D R N L 0) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, hr₁, rdi₁, rsi₁, rdx₁, rcx₁, m₁⟩ := encPre_ok h
  obtain ⟨s₂, run₂, rcx₂, r8₂, r9₂, g₂, m₂, rd₂, wr₂⟩ := startPre_env h hr₁ rdx₁ rcx₁
  have fe : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩] s₀.mem s₁.mem := by rw [m₁]; exact encMem_frame
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr => g₂ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₂ wr₂
  have hf := h.fargsD hr₂.rd hr₂.wr hr₂.rsp (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rsi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdx₁]) rcx₂ r8₂ r9₂
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], hf, hr₂.rsp, ?_⟩
  refine WP.mono (finr_call v _ hf) fun s₃ h₃ => ?_
  have hr₃ := hr₂.keep h₃.saved h₃.rd h₃.wr
  -- What S2V's start writes.
  have fz : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have f₃ : Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s₂.mem s₃.mem := by
    rw [← hr₂.rsp]; exact h₃.frame
  have fs : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₁.mem s₃.mem := by
    refine (fz.mono fun r hr => ?_).trans (f₃.mono fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  have slot {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fs.readW (Region.contains_self _ _) (h.start_dis hd hd') (by decide), m₁]
  obtain ⟨sl₁, sl₂, sl₃, sl₄⟩ := encMem_slots (s₀ := s₀) (A := A) (P := P) (W := W) (N := N) (L := L)
  refine ⟨hr₃.rbx, hr₃.rbp, hr₃.r12, hr₃.r15, hr₃.rsp, hr₃.rd, hr₃.wr, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [slot (by decide) (by decide), sl₁, Nat.mul_zero, k0]
  · rw [slot (by decide) (by decide), sl₂, Nat.sub_zero]
  · rw [slot (by decide) (by decide), sl₃]
  · rw [slot (by decide) (by decide), sl₄]
  · exact (m₁ ▸ encMem_saved).frame fs fun p hp => h.start_dis (by have := saved_ge p hp; omega) (by have := saved_le p hp; omega)
  · refine fe.sub (fun r hr => ⟨r, by simp_all, fun _ h => h⟩) |>.trans (fs.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · -- `CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>`.
    have f₂ : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₂.mem :=
      (fe.mono fun r hr => by simp_all).trans (fz.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
    have ctx {d n : Nat} (hd : d + n ≤ 512) :
        Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (e.c_w.sub_left (Offset.sub_base C hd)).sub_right (e.sW (by decide))
        · exact h.c_d.sub_left (Offset.sub_base C hd)) (by omega)
    have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
      rw [← zero2_bytes s₁.mem (W + BitVec.ofNat 64 16), m₂]
      exact bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (e.d_w.sub_right (e.sW (by decide))).symm) (by decide)
    have hd : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Cmac.zeros 16 := by rw [m₂]; exact zero2_bytes _ _
    have hk1 := ctx (d := 240) (n := 16) (by decide)
    have hk2 := ctx (d := 256) (n := 16) (by decide)
    have hs := ctx (d := 0) (n := 16 * (R + 1)) (by omega)
    rw [k0] at hs
    rw [List.take_zero, h₃.out, mn, hz, hd, hk1, hk2, hs, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart,
      Spec.Siv.ctxMac, Spec.Siv.schedCiph, show Spec.Siv.zero = [] ++ Spec.Cmac.zeros 16 from rfl,
      Siv.cmacWith_split _ _ _ rfl (by decide) (Or.inl rfl), chain_blocks_nil,
      Proof.Cmac.xor_comm (Spec.Cmac.zeros 16)]
    simp only [xor_lastBlock_zeros]
    rfl

/-! ## The components of associated data -/

/-- The slice the `i`-th descriptor at `A` lists. -/
def comp (m : Mem) (A : Addr) (i : Nat) : Region :=
  ⟨m.readW (A + BitVec.ofNat 64 (16 * i)) 64, (m.readW (A + BitVec.ofNat 64 (16 * i + 8)) 64).toNat⟩

theorem listed_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Sig.listed 64 m .u8 A N)[i]'(by simp [Sig.listed, hi]) = comp m A i := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, BitVec.setWidth_eq, Elem.size, Nat.mul_one, comp,
    Offset.add_add]
  rw [Nat.mul_comm]

theorem comp_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) : comp m A i ∈ Sig.listed 64 m .u8 A N := by
  rw [← listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N).take (i + 1) =
      (Spec.Siv.components 64 m A N).take i ++ [Spec.Aes.bytesAt m (comp m A i).base (comp m A i).len] := by
  have hl : i < (Spec.Siv.components 64 m A N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, listed_getElem m A hi]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-! ## S2V over the associated data -/

theorem EPre.N_lt (h : EPre s₀ C A P W D R N L) : N < 2 ^ 64 := by have := h.wA; omega

/-- The descriptors are as on entry. -/
theorem AInv.desc (h : EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : AInv s₀ C A P W D R N L i s) {d : Nat}
    (hd : d + 8 ≤ N * 16) : s.mem.readW (A + BitVec.ofNat 64 d) 64 = s₀.mem.readW (A + BitVec.ofNat 64 d) 64 :=
  hi.frame.readW (Offset.contains_base A hd (by have := h.wA; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.desc_w.sub_right (h.env.sW (by decide))
    · exact h.desc_d
    · exact h.stk_desc.symm) (by decide)

theorem AInv.keep {i : Nat} {s s' : State} (hi : AInv s₀ C A P W D R N L i s)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    AInv s₀ C A P W D R N L i s' :=
  ⟨by rw [hg _ (by decide), hi.rbx], by rw [hg _ (by decide), hi.rbp], by rw [hg _ (by decide), hi.r12],
    by rw [hg _ (by decide), hi.r15], by rw [hg _ (by decide), hi.rsp], by rw [hrd, hi.rd], by rw [hwr, hi.wr], hi.le,
    hm ▸ hi.ads, hm ▸ hi.left, hm ▸ hi.d208, hm ▸ hi.d216, hm ▸ hi.saved, hm ▸ hi.frame, hm ▸ hi.acc⟩

/-- The address of the next descriptor. -/
theorem adLoad_wp (h : EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : AInv s₀ C A P W D R N L i s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 adsOff))]) s fun s' => AInv s₀ C A P W D R N L i s' ∧
      s'.gpr .rax = A + BitVec.ofNat 64 (16 * i) ∧ s'.mem = s.mem := by
  have rA := h.env.inRW hi.rd hi.wr (d := adsOff) (n := 8) (by decide)
  refine WP.of_runBlock ⟨s.setReg .rax (A + BitVec.ofNat 64 (16 * i)), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hi.r15, rA, ite_true, hi.ads], ?_, gpr_setReg_self _ _ _, mem_setReg _ _ _⟩
  exact hi.keep (fun r hr => gpr_setReg_of_ne _ _ hr) (mem_setReg _ _ _) (rd_setReg _ _ _) (wr_setReg _ _ _)

/-- The component's address and length from its descriptor. -/
theorem adDesc_wp (h : EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : AInv s₀ C A P W D R N L i s) (hrax : s.gpr .rax = A + BitVec.ofNat 64 (16 * i)) :
    WP isa (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) s fun s' =>
      Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s' ∧ s'.mem = s.mem := by
  have c₀ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have c₈ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i + 8)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have d₀ := hi.desc h (d := 16 * i) (by omega)
  have d₈ := hi.desc h (d := 16 * i + 8) (by omega)
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, rd_setReg, wr_setReg, mem_setReg, ite_true,
      ite_false, hrax, Offset.add_add, Nat.add_zero, c₀, c₈]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, ite_true, ite_false, hi.rbx, hi.rbp, hi.r12,
    hi.r15, hi.rsp, comp, d₀, d₈]
  · exact BitVec.eq_of_toNat_eq (by rw [toNat_ofNat (BitVec.isLt _)])
  all_goals first | rfl | exact hi.rd | exact hi.wr

/-- One component: its descriptor read (`adNext_ok`), its CMAC into the
working space (`cmacOf_wp`) and the step of S2V (`adStep_wp`). -/
theorem adBody_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : AInv s₀ C A P W D R N L i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep))) s
      fun s' => AInv s₀ C A P W D R N L (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N)) := by
  have e := h.env
  have hN := h.N_lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  rw [show adNext = [.mov .rax (.mem (at_ .r15 adsOff))] ++
    [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))] from rfl]
  refine WP.seq (WP.block_append (WP.mono (adLoad_wp h hi) fun s₀' ⟨hi₀, rax₀, m₀⟩ =>
    WP.mono (adDesc_wp h hiN hi₀ rax₀) fun s₁ h₁ => ?_))
  obtain ⟨hr₁, m₁'⟩ := h₁
  have m₁ : s₁.mem = s.mem := by rw [m₁', m₀]
  refine WP.seq (WP.mono (cmacOf_wp v hQ hr₁) fun s₂ h₂ => ?_)
  have hr₂ := h₂.regs
  refine WP.mono (adStep_wp hr₂.r12 hr₂.r15 (by rw [hr₂.wr]; exact h.dw) (by rw [hr₂.wr]; exact e.workIn) e.d_w e.wD
    e.wW) fun s₃ ⟨b₃, g₃, rd₃, wr₃, z₃, acc₃, ads₃, left₃, f₃⟩ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 32⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16] s.mem
      s₂.mem := m₁ ▸ h₂.frame
  -- The slots outside what the CMAC writes.
  have sl₂ {d : Nat} (hd : d + 8 ≤ 128 ∨ 160 ≤ d) (hd' : d + 8 ≤ 256) :
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (e.stk_w.sub_right (e.sW (by omega))).symm) (by decide)
  -- And outside what the step writes.
  have dis₃ {d : Nat} (hd : d + 8 ≤ 112 ∨ (128 ≤ d ∧ d + 8 ≤ 224) ∨ 232 ≤ d) (hd' : d + 8 ≤ 2560) :
      ∀ r ∈ [(⟨D, 16⟩ : Region), ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩],
        Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (e.d_w.sub_right (e.sW hd')).symm
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
  have sl₃ {d : Nat} (hd : (160 ≤ d ∧ d + 8 ≤ 224)) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dis₃ (by omega) (by omega)) (by decide), sl₂ (by omega) (by omega)]
  have hl₂ : s₂.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i) := by
    rw [sl₂ (by decide) (by decide), hi.left]
  have one : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  refine ⟨⟨by rw [b₃, hr₂.rbx], ?_, ?_, ?_, ?_, by rw [rd₃, hr₂.rd], by rw [wr₃, hr₂.wr], hiN, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp]
  · rw [ads₃, sl₂ (by decide) (by decide), hi.ads, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.add_add, Nat.mul_succ]
  · rw [left₃, hl₂, one, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [sl₃ (by decide), hi.d208]
  · rw [sl₃ (by decide), hi.d216]
  · refine (hi.saved.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_
    · have := saved_ge p hp; have := saved_le p hp
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (e.stk_w.sub_right (e.sW (by omega))).symm
    · have := saved_ge p hp; have := saved_le p hp
      exact dis₃ (by omega) (by omega)
  · refine (hi.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  · -- `D = dbl(D) ⊕ CMAC(Sᵢ)`.
    have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s.mem D 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.stk_d.symm) (by decide)
    have hf3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact e.c_w.sub_right (e.sW (by decide))
      · exact h.c_d
      · exact e.stk_c.symm
    have hq3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨(comp s₀.mem A i).base, (comp s₀.mem A i).len⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hQ.p_w.sub_right (e.sW (by decide))
      · exact hQ.d_p.symm
      · exact hQ.stk_p.symm
    have o₂ := h₂.out
    rw [m₁, ctxMac_frame hi.frame hf3 hRb, bytesAt_frame hi.frame hq3 (by have := hQ.lt; omega)] at o₂
    rw [acc₃, dD, o₂, hi.acc, components_take_succ s₀.mem A hiN, s2vAcc_snoc]
    rfl
  · rw [z₃, hl₂, one, Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Whether there are any components: ZF is set if not. -/
theorem adsHead_wp (h : EPre s₀ C A P W D R N L) {s : State} (hs : AInv s₀ C A P W D R N L 0 s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) s fun s₁ =>
      AInv s₀ C A P W D R N L 0 s₁ ∧ s₁.zf = some (decide (N = 0)) := by
  have hN := h.N_lt
  have rL := h.env.inRW hs.rd hs.wr (d := leftOff) (n := 8) (by decide)
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 leftOff)),
      .alu .test .rax (.reg .rax)] s = some s₁ ∧ s₁.zf = some (decide (N = 0)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.ea,
        offset_nat, Option.map_some, Option.bind_some, hs.r15, rL, ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags]
      simp only [gpr_setReg_self]
      rw [hs.left, Nat.sub_zero, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hN]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, hs.keep g₁ m₁ rd₁ wr₁, zf₁⟩

/-- S2V over all the components, if there are any. -/
theorem ads_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) {s : State} (hs : AInv s₀ C A P W D R N L 0 s) :
    WP isa (s2vAds v.callee v.ctr.callee v.ctr.suffix) s (AInv s₀ C A P W D R N L N) := by
  refine WP.seq (WP.mono (adsHead_wp h hs) fun s₁ ⟨hs₁, zf₁⟩ => ?_)
  refine WP.ite (decide (N = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hN0 : N = 0 := of_decide_eq_true hb
    rw [hN0] at hs₁ ⊢; exact hs₁
  have hN0 : 0 < N := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = N - i ∧ i < N ∧ AInv s₀ C A P W D R N L i t) ?_ (N - 0) s₁
    ⟨0, rfl, hN0, hs₁⟩
  rintro n t ⟨i, rfl, hiN, hi⟩
  refine WP.mono (adBody_wp v h hiN hi) fun t' ⟨hi', hz⟩ => ?_
  by_cases he : i + 1 = N
  · exact Or.inl ⟨by simp [eval, hz, he], he ▸ hi'⟩
  · exact Or.inr ⟨by simp [eval, hz, he], N - (i + 1), by omega, i + 1, rfl, by omega, hi'⟩

/-- What S2V of the associated data leaves: the registers and slots as
`sealTail_wp` and `openTail_wp` take them, the saved registers, and `D`. -/
structure SDone (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  spre : SPre s₀ C D P W R L s
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.components 64 s₀.mem A N)

/-- The data and its length back in their registers. -/
theorem adsEnd_wp (h : EPre s₀ C A P W D R N L) {s : State} (hs : AInv s₀ C A P W D R N L N s) :
    WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
      (SDone s₀ C A P W D R N L) := by
  obtain ⟨s₃, run₃, r13, r14, g₃, m₃, rd₃, wr₃⟩ := ctrEnd_ok h.env hs.r15 hs.rd hs.wr hs.d208 hs.d216
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨?_, ?_, ?_, r13, r14, ?_, ?_, by rw [rd₃, hs.rd], by rw [wr₃, hs.wr]⟩,
    m₃ ▸ hs.d208, m₃ ▸ hs.d216⟩, m₃ ▸ hs.saved, m₃ ▸ hs.frame, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hs.rbx]
  · rw [g₃ _ (by decide) (by decide), hs.rbp]
  · rw [g₃ _ (by decide) (by decide), hs.r12]
  · rw [g₃ _ (by decide) (by decide), hs.r15]
  · rw [g₃ _ (by decide) (by decide), hs.rsp]
  · have hl : (Spec.Siv.components 64 s₀.mem A N).length = N := by simp [Spec.Siv.components, Sig.listed]
    rw [m₃, hs.acc, List.take_of_length_le (Nat.le_of_eq hl)]

theorem encS2v_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encS2v v.callee v.ctr.callee v.ctr.suffix) s₀ (SDone s₀ C A P W D R N L) :=
  WP.seq (WP.mono (start_wp v.ctr h) fun _ h₀ => WP.seq (WP.mono h₀.2.2 fun _ h₁ =>
    WP.seq (WP.mono (ads_wp v h h₁) fun _ h₂ => adsEnd_wp h h₂)))

/-! ## The whole functions -/

/-- The key context, the data and the return address are outside what S2V
of the associated data writes. -/
theorem EPre.sdone_dis (h : EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨C, 512⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨P, L⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨W, 16⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r) := by
  have e := h.env
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact e.c_w.sub_right (e.sW (by decide))
  · exact h.c_d
  · exact e.stk_c.symm
  · exact e.p_w.sub_right (e.sW (by decide))
  · exact e.d_p.symm
  · exact e.stk_p.symm
  · exact Offset.base_disjoint W (by decide) (by have := e.wW; omega)
  · exact (e.d_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (e.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact e.ret_w.sub_right (e.sW (by decide))
  · exact e.ret_d
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

/-- The return address is outside what the ends write. -/
theorem EPre.ret_end (h : EPre s₀ C A P W D R N L) :
    ∀ r ∈ endRegions W P L (s₀.gpr .rsp), (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.env.ret_p
  · exact h.env.ret_w
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

variable {T : Addr}

/-- Disjoint ranges are separate. -/
theorem sep_of_disjoint {a b : Addr} {n k n' k' : Nat} (h : (⟨a, n'⟩ : Region).Disjoint ⟨b, k'⟩)
    (hn : n ≤ n') (hk : k ≤ k') : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- The synthetic IV `T`, whose address is the stack argument before the
working space's: the 16 bytes at `T` are apart from the data, the working
space, `D`, the stack and the return address, and the two stack arguments
are apart from the data, the working space and `D`. -/
structure SivArg (s₀ : State) (P W D T : Addr) (L : Nat) : Prop where
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 8) 8
  args_p : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨P, L⟩
  args_w : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  args_d : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, 16⟩
  tIn : (⟨T, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  t_p : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩
  t_w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  t_d : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_t : (below (s₀.gpr .rsp) 16).Disjoint ⟨T, 16⟩
  ret_t : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩
  wT : T.toNat + 16 ≤ 2 ^ 64

/-- What `encrypt` and `decrypt` write: the data, the working space, `D` and
the stack. -/
abbrev allRegions (W D P : Addr) (L : Nat) (sp : Addr) : List Region :=
  [⟨P, L⟩, ⟨W, 2560⟩, ⟨D, 16⟩, below sp 16]

/-- The permissions, as a postcondition. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

theorem EPre.all_sub (h : EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      ∃ r' ∈ allRegions W D P L (s₀.gpr .rsp), Region.Sub r r') ∧
    (∀ r ∈ endRegions W P L (s₀.gpr .rsp), ∃ r' ∈ allRegions W D P L (s₀.gpr .rsp), Region.Sub r r') := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.env.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩

/-- `encrypt` but for the copy of the IV: the IV at `W`, the ciphertext at
`P`, and nothing written but the data, the working space, `D` and the stack. -/
theorem encryptCore_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encryptCore v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Frame (allRegions W D P L (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  obtain ⟨sub₁, sub₂⟩ := h.all_sub
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (sealTail_wp v e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, (hs.frame.sub sub₁).trans (f'.sub sub₂), ?_⟩)
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide), hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
    rw [Spec.Siv.encryptWith_eq]
    exact out'

/-- The stack arguments are outside what the code writes. -/
theorem SivArg.args_dis (hT : SivArg s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) : ∀ r ∈ allRegions W D P L (s₀.gpr .rsp),
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.args_p.sub_left hs
  · exact hT.args_w.sub_left hs
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega)

/-- The stack arguments are outside what S2V writes. -/
theorem SivArg.args_dis₁ (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hT.args_w.sub_left hs).sub_right (h.env.sW (by decide))
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega)

/-- The IV's bytes are outside what S2V writes. -/
theorem SivArg.s2v_dis (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨T, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hT.t_w.sub_right (h.env.sW (by decide))
  · exact hT.t_d
  · exact hT.stk_t.symm

/-- The copy of the IV from the working space at `W` to `T`. -/
theorem sivOut_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8)
    (iW₀ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 0) 8)
    (iW₈ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 8) 8)
    (oT₀ : InRegions u.wr (T + BitVec.ofNat 64 0) 8) (oT₈ : InRegions u.wr (T + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivOut u = some u' ∧
      u'.mem = (u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (T + BitVec.ofNat 64 8)
        ((u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).readW
          (W + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivOut, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, a16, i8, i16, iW₀, iW₈, oT₀, oT₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What the copy of the IV reads after `encryptCore`: the stack arguments. -/
structure OutPre (s₀ : State) (W T : Addr) (u : State) : Prop where
  sp : u.gpr .rsp = s₀.gpr .rsp
  a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8
  i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8

theorem outPre_of (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {u : State}
    (g : gprPreserved s₀ u) (f : Frame (allRegions W D P L (s₀.gpr .rsp)) s₀.mem u.mem) (rd : u.rd = s₀.rd)
    (wr : u.wr = s₀.wr) : OutPre s₀ W T u := by
  have sp : u.gpr .rsp = s₀.gpr .rsp := g.1 .rsp (by decide)
  refine ⟨sp, ?_, ?_, by rw [rd, wr, sp]; exact hT.argIn, by rw [rd, wr, sp]; exact h.argIn⟩
  · rw [sp, ← hT.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 8) (by decide) (by decide)) (by decide)
  · rw [sp, ← h.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 16) (by decide) (by decide)) (by decide)

/-- `encryptCore` ends where the copy of the IV can read its stack arguments. -/
theorem encryptCore_out (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (encryptCore v.callee v.ctr.callee v.ctr.suffix) s₀ (OutPre s₀ W T) :=
  WP.mono (WP.rdwr (encryptCore_wp v h)) fun _ ⟨⟨g, f, _⟩, rd, wr⟩ => outPre_of h hT g f rd wr

/-- The first two loads of `sivOut`: the addresses of `siv` and the working space. -/
theorem sivOutHead_wp {u : State} (hu : OutPre s₀ W T u) :
    WP isa (.block (sivOut.take 2)) u fun u' => u'.gpr .rax = T ∧ u'.gpr .r10 = W :=
  WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, sivOut, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hu.i8, hu.a8, hu.i16, hu.a16]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg]⟩

theorem encrypt_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) :
    WP isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  refine WP.seq (WP.mono (WP.rdwr (encryptCore_wp v h)) fun u ⟨⟨⟨g, ret⟩, f, out⟩, rd, wr⟩ => ?_)
  have hu := outPre_of h hT ⟨g, ret⟩ f rd wr
  have iW (d : Nat) (hd : d + 8 ≤ 16) : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 d) 8 :=
    e.inRW rd wr (by omega)
  have oT (d : Nat) (hd : d + 8 ≤ 16) : InRegions u.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := hT.wT; omega)⟩
  obtain ⟨u', run, m', g', -, -⟩ := sivOut_ok hu.a8 hu.a16 hu.i8 hu.i16 (iW 0 (by decide)) (iW 8 (by decide))
    (oT 0 (by decide)) (oT 8 (by decide))
  refine WP.of_runBlock ⟨u', run, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g' r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
      (by rintro rfl; revert hr; decide), g r hr]
  · -- The return address, apart from `T`.
    have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [fT.readW (Region.contains_self _ _) (one_out hT.ret_t) (by decide), ret]
  · have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [out, bytesAt_frame fT (one_out hT.t_p.symm) (by have := e.lt; omega)]
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (hT.t_w.sub_right (e.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- The copy of the IV from `T` to the working space at `W`. -/
theorem sivIn_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (r15 : u.gpr .r15 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (iT₀ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 0) 8)
    (iT₈ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 8) 8)
    (oW₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8) (oW₈ : InRegions u.wr (W + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivIn u = some u' ∧
      u'.mem = (u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 8)
        ((u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).readW
          (T + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivIn, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, r15, i8, iT₀, iT₈, oW₀, oW₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The address of `siv`, on the stack, after S2V. -/
theorem SDone.argT (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = T := by
  rw [hs.spre.regs.rsp, ← hT.arg]
  exact hs.frame.readW (Region.contains_self _ _) (hT.args_dis₁ h (d := 8) (by decide) (by decide)) (by decide)

/-- The first load of `sivIn`: the address of `siv`. -/
theorem sivInHead_wp (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) :
    WP isa (.block (sivIn.take 1)) s fun s' => s'.gpr .rax = T ∧ s'.gpr .r15 = W := by
  have hr := hs.spre.regs
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  exact WP.of_runBlock ⟨_, by
    simp only [sivIn, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, ite_true, i8, hs.argT h hT]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg, hr.r15]⟩

/-- What `sivIn` keeps of S2V's end, with the received IV now at `W`. -/
theorem sivIn_wp (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) :
    WP isa (.block sivIn) s fun s' => SPre s₀ C D P W R L s' ∧ Spill.Saved s'.mem W s₀.gpr saved ∧
      Frame [⟨W, 16⟩] s.mem s'.mem ∧ Spec.Aes.bytesAt s'.mem W 16 = Spec.Aes.bytesAt s₀.mem T 16 := by
  have e := h.env
  have hr := hs.spre.regs
  have a8 := hs.argT h hT
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  have iT (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 d) 8 := by
    rw [hr.rd, hr.wr]; exact ⟨_, hT.tIn, Offset.contains_base T hd (by have := hT.wT; omega)⟩
  obtain ⟨s', run, m', g', rd', wr'⟩ := sivIn_ok a8 hr.r15 i8 (iT 0 (by decide)) (iT 8 (by decide))
    (e.inW hr.wr (d := 0) (by decide)) (e.inW hr.wr (d := 8) (by decide))
  have fW : Frame [⟨W, 16⟩] s.mem s'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' W _ _
  have slot {d : Nat} (hd : 16 ≤ d) (hd' : d + 8 ≤ 2560) :
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fW.readW (Region.contains_self _ _) (one_out (Offset.disjoint_base W (by omega) (by have := e.wW; omega)))
      (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨hr.keep (fun r hr' => g' r (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide)) rd' wr', by rw [slot (by decide) (by decide), hs.spre.d208],
      by rw [slot (by decide) (by decide), hs.spre.d216]⟩, hs.saved.frame fW fun p hp => one_out
        (Offset.disjoint_base W (by have := saved_ge p hp; omega) (by have := saved_le p hp; have := e.wW; omega)),
    fW, ?_⟩
  have sp8 : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    sep_of_disjoint ((hT.t_w.sub_left (Offset.sub_base T (d := 8) (n := 8) (by decide))).sub_right
      (Region.sub_prefix (len := 16) (by decide))) (by decide) (by decide)
  rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  exact bytesAt_frame hs.frame (hT.s2v_dis h) (by decide)

theorem decrypt_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem T 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  have wC := one_out (e.c_w.sub_right (Region.sub_prefix (len := 16) (by decide)))
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.seq (WP.mono (sivIn_wp h hT hs)
    fun s₁ ⟨sp₁, sv₁, f₁, v₁⟩ => WP.mono (openTail_wp v e h.cp h.pw sp₁ sv₁)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩))
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide),
      f₁.readW c (one_out (e.ret_w.sub_right (Region.sub_prefix (by decide)))) (by decide),
      hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame f₁ wC hRb, ctxCiph_frame f₁ wC hRb,
      bytesAt_frame f₁ (one_out (e.p_w.symm.sub_left (Region.sub_prefix (by decide))).symm) (by have := e.lt; omega),
      bytesAt_frame f₁ (one_out (e.d_w.sub_right (Region.sub_prefix (by decide)))) (by decide), v₁,
      ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
    rw [Spec.Siv.decryptWith_eq]
    exact out'

end VG.Proof.AesSiv.X86_64
