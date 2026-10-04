import VerifiedGarbage.Proof.AesSiv.AArch64.Open
import VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd
import VerifiedGarbage.Proof.AesSiv.AArch64.Call
import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV on AArch64: `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

Both save the registers in the working space and keep the arguments in
callee-saved registers (`encPre`), start S2V into `D = W + 2560` with the
CMAC of the zero block (`start_wp`), absorb the components of associated
data, one per iteration (`ads_wp`), and then go on as `sealTail_wp` and
`openTail_wp` say from S2V's state.

The proofs are on the state whose writable regions are the data, the first
2560 bytes of the working space and `D` (`EPre`); `Verified.lean` moves them
to the shared contracts, whose working space is one region of 2576 bytes.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs toNat_ofNat toNat_add_lt eval_zero eval_nonzero)

/-- What `encrypt` and `decrypt` need of their arguments, on the state with
narrowed permissions: the key context `C`, the rounds `R`, the `N`
descriptors at `A`, the data `P` (`L` bytes), the working space `W`, and
S2V's state `D` after its first 2560 bytes. Each component a descriptor
lists is a message as the data is (`comps`). -/
structure EPre (s₀ : State) (C A P W D : Addr) (R N L : Nat) : Prop where
  env : Env s₀ C D P W R L
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  dw : (⟨D, 16⟩ : Region) ∈ s₀.wr
  x0 : s₀.gpr .x0 = C
  x1 : s₀.gpr .x1 = BitVec.ofNat 64 R
  x2 : s₀.gpr .x2 = A
  x3 : s₀.gpr .x3 = BitVec.ofNat 64 N
  x4 : s₀.gpr .x4 = P
  x5 : s₀.gpr .x5 = BitVec.ofNat 64 L
  x6 : s₀.gpr .x6 = W
  descIn : (⟨A, N * 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  desc_w : (⟨A, N * 16⟩ : Region).Disjoint ⟨W, 2560⟩
  desc_d : (⟨A, N * 16⟩ : Region).Disjoint ⟨D, 16⟩
  wA : A.toNat + N * 16 ≤ 2 ^ 64
  comps : ∀ r ∈ Sig.listed 64 s₀.mem .u8 A N, Env s₀ C D r.base W R r.len

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat}

theorem EPre.N_lt (h : EPre s₀ C A P W D R N L) : N < 2 ^ 64 := by have := h.wA; omega

/-! ## The save and S2V's first state -/

/-- The memory after the save and the zeroing of the zero block and `D`. -/
def startMem (s₀ : State) (W D : Addr) : Mem :=
  Proof.Cmac.zero2 (Proof.Cmac.zero2 (Spill.saveMem s₀.mem W s₀.gpr saved) (W + BitVec.ofNat 64 zOff)) D

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 248 := by decide

/-- The registers after the save and the moves of the arguments. -/
structure Started (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = C
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = W + BitVec.ofNat 64 zOff
  x4 : s.gpr .x4 = BitVec.ofNat 64 16
  x5 : s.gpr .x5 = W + BitVec.ofNat 64 csOff
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x24 : s.gpr .x24 = A
  x25 : s.gpr .x25 = BitVec.ofNat 64 N
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = startMem s₀ W D

theorem start_ok (h : EPre s₀ C A P W D R N L) :
    WP isa (.block (encPre ++ startPre)) s₀ (Started s₀ C A P W D R N L) := by
  have e := h.env
  have hwD := e.wD
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add, ← e.hD]; exact ⟨_, h.dw, Offset.contains_base _ hd (by omega)⟩
  have z₀ := e.inW (s := s₀) rfl (d := zOff) (n := 8) (by decide)
  have z₁ := e.inW (s := s₀) rfl (d := zOff + 8) (n := 8) (by decide)
  have d₀ := inD 0 (by decide)
  have d₁ := inD 8 (by decide)
  rw [Nat.add_zero] at d₀
  rw [show encPre ++ startPre = Spill.saveCode .x6 saved ++
    ([mov .x19 .x6, mov .x20 .x0, mov .x21 .x1, mov .x24 .x2, mov .x25 .x3, mov .x26 .x4, mov .x27 .x5] ++
      startPre) from rfl]
  refine Spill.save_ok (fun p hp => saved_fits.1 p hp) (fun p hp => by
    have := saved_bound p hp; rw [h.x6]; exact e.inW rfl (by omega)) ?_
  refine WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [startPre, mov, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write,
      mem_write, rd_write, wr_write, ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq, k0, h.x6, z₀, z₁,
      d₀, d₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  all_goals try simp (config := {decide := true}) only [gpr_write, ite_true, ite_false, h.x0, h.x1, h.x2, h.x3,
    h.x4, h.x5, Proof.CmacAes.Stream.AArch64.mz16, e.hD, BitVec.setWidth_eq]
  simp only [mem_write, startMem, Proof.Cmac.zero2, Mem.writeW, Proof.CmacAes.Stream.AArch64.mz0, Offset.add_add]
  rfl

/-- The arguments of `vg_cmac_aes_finalize` for S2V's first state: the
context as the key, the state `D`, the zero block at `W + 16` and the working
space at `W + 256`. -/
theorem Started.fargs (h : EPre s₀ C A P W D R N L) {s : State} (hs : Started s₀ C A P W D R N L s) :
    FArgs s C D (W + BitVec.ofNat 64 zOff) (W + BitVec.ofNat 64 csOff) 16 R :=
  h.env.fargs' hs.rd hs.wr (h.env.d_w.sub_right (h.env.sW (by decide))) h.c_d h.env.wD (cov_base h.dw (by simp))
    (h.env.d_w.sub_right (h.env.sW (d := zOff) (n := 16) (by decide))).symm
    (Offset.disjoint W (by decide) (by decide) (by have := h.env.wW; omega))
    (by rw [toNat_add_lt W h.env.wW (show zOff < 2560 by decide)]; have := h.env.wW; simp only [zOff]; omega)
    (Covers.right (cov_off h.env.workIn (by simp [zOff]))) (by decide)
    hs.x0 hs.x1 hs.x2 hs.x3 hs.x4 hs.x5

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
    Proof.Cmac.bytesAt_length])

/-- The state before the `i`-th component of associated data (and, for
`i = N`, after the last): `D` is S2V's state of the first `i`, `x24` and
`x25` the next descriptor's address and how many are left, and the data in
`x26` and `x27`. -/
structure AInv (s₀ : State) (C A P W D : Addr) (R N L : Nat) (i : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x24 : s.gpr .x24 = A + BitVec.ofNat 64 (16 * i)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (N - i)
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : i ≤ N
  saved : Spill.Saved W s₀.gpr saved s.mem
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) ((Spec.Siv.components 64 s₀.mem A N).take i)

/-- The save, then S2V's first state `D = AES-CMAC(K1, <zero>)` with
`vg_cmac_aes_finalize` of the zero block from a zero state. -/
theorem start_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) {s₂ : State}
    (h₂ : Started s₀ C A P W D R N L s₂) :
    WP isa (callFinalize v.ctr.callee v.ctr.suffix) s₂ (AInv s₀ C A P W D R N L 0) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  refine WP.mono (finr_call v.ctr _ (h₂.fargs h)) fun s₃ h₃ => ?_
  have g₃ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s₂.gpr r := h₃.saved r hr h30
  -- What the save and S2V's start write.
  have fs : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₂.mem := by
    rw [h₂.mem, startMem]
    refine ((Spill.saveMem_frame (lo := 16) (n := 2544) (fun p hp => by have := saved_ge p hp; omega)
      (by decide) _ _ _).mono (by simp)).trans (((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have f₃ : Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 csOff, 2176⟩] s₂.mem s₃.mem := h₃.frame
  have fall : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₃.mem :=
    fs.trans (f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩)
  refine ⟨by rw [g₃ _ (by decide) (by decide), h₂.x19], by rw [g₃ _ (by decide) (by decide), h₂.x20],
    by rw [g₃ _ (by decide) (by decide), h₂.x21], by rw [g₃ _ (by decide) (by decide), h₂.x24, Nat.mul_zero, k0],
    by rw [g₃ _ (by decide) (by decide), h₂.x25, Nat.sub_zero], by rw [g₃ _ (by decide) (by decide), h₂.x26],
    by rw [g₃ _ (by decide) (by decide), h₂.x27], by rw [h₃.sp, h₂.sp], by rw [h₃.rd, h₂.rd],
    by rw [h₃.wr, h₂.wr], Nat.zero_le _, ?_, fall, ?_⟩
  · -- The slots, past what S2V's start writes.
    have sv0 := Spill.saveMem_saved saved_fits s₀.mem W s₀.gpr
    have sv1 := sv0.frame (Proof.Cmac.frame_store2 (W + BitVec.ofNat 64 zOff) 0 0) fun p hp r hr => by
      have := saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by simp only [zOff]; omega) (by omega) (by decide)
    have sv2 := sv1.frame (Proof.Cmac.frame_store2 D 0 0) fun p hp r hr => by
      have := saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact (e.d_w.sub_right (e.sW (by omega))).symm
    have sv : Spill.Saved W s₀.gpr saved s₂.mem := by rw [h₂.mem]; exact sv2
    refine sv.frame f₃ fun p hp r hr => ?_
    have := saved_ge p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (e.d_w.sub_right (e.sW (by omega))).symm
    · exact Offset.disjoint W (by simp only [csOff]; omega) (by omega) (by decide)
  · -- `CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>`.
    have ctx {d n : Nat} (hd : d + n ≤ 512) :
        Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
      Proof.Cmac.bytesAt_frame fs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (e.c_w.sub_left (Offset.sub_base C hd)).sub_right (e.sW (by decide))
        · exact h.c_d.sub_left (Offset.sub_base C hd)) (by omega)
    have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 zOff) 16 = Spec.Cmac.zeros 16 := by
      have fr : Frame [⟨D, 16⟩] (Proof.Cmac.zero2 (Spill.saveMem s₀.mem W s₀.gpr saved) (W + BitVec.ofNat 64 zOff))
          (startMem s₀ W D) := Proof.Cmac.frame_store2 _ _ _
      rw [h₂.mem, Proof.Cmac.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (e.d_w.sub_right (e.sW (d := zOff) (n := 16) (by decide))).symm) (by decide)]
      exact Proof.Cmac.zero2_bytes _ _
    have hd : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Cmac.zeros 16 := by
      rw [h₂.mem, startMem]; exact Proof.Cmac.zero2_bytes _ _
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

/-- The descriptors are as on entry. -/
theorem AInv.desc (h : EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : AInv s₀ C A P W D R N L i s) {d : Nat}
    (hd : d + 8 ≤ N * 16) : s.mem.readW (A + BitVec.ofNat 64 d) 64 = s₀.mem.readW (A + BitVec.ofNat 64 d) 64 :=
  hi.frame.readW (Offset.contains_base A hd (by have := h.wA; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.desc_w.sub_right (h.env.sW (by decide))
    · exact h.desc_d) (by decide)

/-- The component's address and length from its descriptor. -/
theorem adNext_wp (h : EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : AInv s₀ C A P W D R N L i s) :
    WP isa (.block adNext) s fun s' =>
      Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s' ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  have c₀ : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 0) 8 := by
    rw [hi.rd, hi.wr, hi.x24, k0]
    exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have c₈ : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 8) 8 := by
    rw [hi.rd, hi.wr, hi.x24, Offset.add_add]
    exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have d₀ := hi.desc h (d := 16 * i) (by omega)
  have d₈ := hi.desc h (d := 16 * i + 8) (by omega)
  rw [adNext]
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_ldr_x (by decide) c₀, runStep_some, runBlock_cons,
      exec_ldr_x (by decide) (by simpa only [gpr_write, rd_write, wr_write, reduceCtorEq, ite_false] using c₈),
      runStep_some, runBlock_nil], ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, hi.sp, hi.rd, hi.wr⟩
    all_goals simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hi.x19, hi.x20, hi.x21, mem_write, hi.x24,
      Offset.add_add, Nat.add_zero, BitVec.setWidth_eq, comp, d₀, d₈]
    exact Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq rfl
  · intro r a b; simp [gpr_write, a, b]
  · rfl

/-- One component: its descriptor read (`adNext_wp`), its CMAC into the
working space (`cmacOf_wp`) and the step of S2V (`adStep_wp`). -/
theorem adBody_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N)
    {s : State} (hi : AInv s₀ C A P W D R N L i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep))) s
      fun s' => AInv s₀ C A P W D R N L (i + 1) s' := by
  have e := h.env
  have hN := h.N_lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  refine WP.seq (WP.mono (adNext_wp h hiN hi) fun s₁ ⟨hr₁, g₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (cmacOf_wp v hQ hr₁) fun s₂ h₂ => ?_)
  have hr₂ := h₂.regs
  refine WP.mono (adStep_wp hr₂.x19 e.hD (by rw [hr₂.wr]; exact h.dw) (by rw [hr₂.wr]; exact e.workIn) e.d_w e.wD
    e.wW) fun s₃ ⟨g₃, x24₃, x25₃, sp₃, rd₃, wr₃, acc₃, f₃⟩ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₂.mem := m₁ ▸ h₂.frame
  have k₂ (r : Reg) (hr : r ∈ [Reg.x24, .x25, .x26, .x27]) : s₂.gpr r = s.gpr r := by
    rw [h₂.hold r hr, g₁ r (dec_ne (by decide) hr) (dec_ne (by decide) hr)]
  have g₃' (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21, .x26, .x27]) : s₃.gpr r = s₂.gpr r :=
    g₃ r (dec_ne (by decide) hr) (dec_ne (by decide) hr) (dec_ne (by decide) hr) (dec_ne (by decide) hr)
      (dec_ne (by decide) hr) (dec_ne (by decide) hr)
  have sub₂ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩],
      ∃ r' ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  refine ⟨by rw [g₃' _ (by decide), hr₂.x19], by rw [g₃' _ (by decide), hr₂.x20],
    by rw [g₃' _ (by decide), hr₂.x21], ?_, ?_, by rw [g₃' _ (by decide), k₂ _ (by decide), hi.x26],
    by rw [g₃' _ (by decide), k₂ _ (by decide), hi.x27], by rw [sp₃, hr₂.sp], by rw [rd₃, hr₂.rd],
    by rw [wr₃, hr₂.wr], hiN, ?_, ?_, ?_⟩
  · rw [x24₃, k₂ _ (by decide), hi.x24, Offset.add_add, Nat.mul_succ]
  · rw [x25₃, k₂ _ (by decide), hi.x25, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · refine (hi.saved.frame f₂ fun p hp r hr => ?_).frame f₃ fun p hp r hr => ?_
    · have := saved_ge p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · have := saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact (e.d_w.sub_right (e.sW (by omega))).symm
  · exact (hi.frame.trans (f₂.sub sub₂)).trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · -- `D = dbl(D) ⊕ CMAC(Sᵢ)`.
    have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s.mem D 16 :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.d_w.sub_right (e.sW (by decide))) (by decide)
    have hf3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.c_w.sub_right (e.sW (by decide))
      · exact h.c_d
    have hq3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩],
        (⟨(comp s₀.mem A i).base, (comp s₀.mem A i).len⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hQ.p_w.sub_right (e.sW (by decide))
      · exact hQ.d_p.symm
    have o₂ := h₂.out
    rw [m₁, ctxMac_frame hi.frame hf3 hRb, Proof.Cmac.bytesAt_frame hi.frame hq3 (by have := hQ.lt; omega)] at o₂
    rw [acc₃, dD, o₂, hi.acc, components_take_succ s₀.mem A hiN, s2vAcc_snoc]
    rfl

/-- S2V over all the components, if there are any. -/
theorem ads_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) {s : State}
    (hs : AInv s₀ C A P W D R N L 0 s) :
    WP isa (s2vAds v.callee v.ctr.callee v.ctr.suffix) s (AInv s₀ C A P W D R N L N) := by
  have hN := h.N_lt
  have ev := eval_zero (s := s) (r := .x25) (x := N) hN (by rw [hs.x25, Nat.sub_zero])
  refine WP.ite (decide (N = 0)) ev (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hN0 : N = 0 := of_decide_eq_true hb
    subst hN0; exact hs
  have hN0 : 0 < N := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .nonzero .x .x25)
    (fun (n : Nat) (t : State) => ∃ i, n = N - i ∧ i < N ∧ AInv s₀ C A P W D R N L i t) ?_ (N - 0) s
    ⟨0, rfl, hN0, hs⟩
  rintro n t ⟨i, rfl, hiN, hi⟩
  refine WP.mono (adBody_wp v h hiN hi) fun t' hi' => ?_
  have ev' := eval_nonzero (s := t') (r := .x25) (x := N - (i + 1)) (by omega) hi'.x25
  by_cases he : i + 1 = N
  · refine Or.inl ⟨by rw [ev']; simp [he], he ▸ hi'⟩
  · exact Or.inr ⟨by rw [ev']; simp; omega, N - (i + 1), by omega, i + 1, rfl, by omega, hi'⟩

/-- What S2V of the associated data leaves: the registers as
`sealTail_wp` and `openTail_wp` take them, the saved registers, and `D`. -/
structure SDone (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  spre : SPre s₀ C D P W R L s
  saved : Spill.Saved W s₀.gpr saved s.mem
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.components 64 s₀.mem A N)

/-- The data and its length in `x22` and `x23`. -/
theorem adsEnd_wp {s : State} (hs : AInv s₀ C A P W D R N L N s) :
    WP isa (.block [mov .x22 .x26, mov .x23 .x27]) s (SDone s₀ C A P W D R N L) := by
  obtain ⟨s₃, run₃, x22, x23, g₃, sp₃, m₃, rd₃, wr₃⟩ := ctrEnd_ok hs.x26 hs.x27
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨?_, ?_, ?_, x22, x23, by rw [sp₃, hs.sp], by rw [rd₃, hs.rd],
    by rw [wr₃, hs.wr]⟩, by rw [g₃ _ (by decide) (by decide), hs.x26], by rw [g₃ _ (by decide) (by decide), hs.x27]⟩,
    m₃ ▸ hs.saved, m₃ ▸ hs.frame, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hs.x19]
  · rw [g₃ _ (by decide) (by decide), hs.x20]
  · rw [g₃ _ (by decide) (by decide), hs.x21]
  · have hl : (Spec.Siv.components 64 s₀.mem A N).length = N := by simp [Spec.Siv.components, Sig.listed]
    rw [m₃, hs.acc, List.take_of_length_le (Nat.le_of_eq hl)]

theorem encS2v_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encS2v v.callee v.ctr.callee v.ctr.suffix) s₀ (SDone s₀ C A P W D R N L) := by
  exact WP.seq (WP.mono (start_ok h) fun _ h₀ => WP.seq (WP.mono (start_wp v h h₀) fun _ h₁ =>
    WP.seq (WP.mono (ads_wp v h h₁) fun _ h₂ => adsEnd_wp h₂)))

/-! ## The whole functions -/

/-- The key context, the data and the IV are outside what S2V of the
associated data writes. -/
theorem EPre.sdone_dis (h : EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨C, 512⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨P, L⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨W, 16⟩ : Region).Disjoint r) := by
  have e := h.env
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
  · exact e.c_w.sub_right (e.sW (by decide))
  · exact h.c_d
  · exact e.p_w.sub_right (e.sW (by decide))
  · exact e.d_p.symm
  · exact Offset.base_disjoint W (by decide) (by have := e.wW; omega)
  · exact (e.d_w.sub_right (Region.sub_prefix (by decide))).symm

theorem encrypt_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' =>
      ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -⟩ := h.sdone_dis
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (sealTail_wp v e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', _, out'⟩ => ⟨⟨g', sp'⟩, ?_⟩)
  rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
    Proof.Cmac.bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
  rw [Spec.Siv.encryptWith_eq]
  exact out'

theorem decrypt_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' =>
      ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem W 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, dV⟩ := h.sdone_dis
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (openTail_wp v e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', _, out'⟩ => ⟨⟨g', sp'⟩, ?_⟩)
  rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
    Proof.Cmac.bytesAt_frame hs.frame dP (by have := e.lt; omega), Proof.Cmac.bytesAt_frame hs.frame dV (by decide),
    hs.acc] at out'
  rw [Spec.Siv.decryptWith_eq]
  exact out'

end VG.Proof.AesSiv.AArch64
