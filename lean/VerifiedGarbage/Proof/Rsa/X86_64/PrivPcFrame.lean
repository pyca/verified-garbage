module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCtx
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: the frame

`vg_rsa_private_checked`'s (`PrivFrame.lean`), for this function's frame of
`frameBytes` bytes at `S = rsp - frameBytes`, its slots, and its 16 stack
arguments, at `S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Addresses in the frame -/

/-- The function's stack argument `j`, from the frame at `S = rsp - frameBytes`. -/
theorem ea_argP {t : State} {s : State} (h : t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 frameBytes) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-! ## The precondition, by name -/

/-- `chkPcContract.pre`, by name. -/
structure PreFPc (s : State) : Prop where
  sp1 : stackBytesPc ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 136 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩,
    ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩, ⟨stackArgAddr s 0, 128⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dOpre : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 128⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dis : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dps : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqs : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddps : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddqs : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqis : (⟨stackArg s 10, (stackArg s 11).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dpres : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dsa : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 128⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKi : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dKpre : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint
    ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩ : Region).Disjoint ⟨stackArgAddr s 0, 128⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wI : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wP : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wQ : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDp : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wDq : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wQi : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wS : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  wPre : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  hil : (stackArg s 1).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 3).toNat
  pl2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 5).toNat
  ql2 : (stackArg s 5).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 7).toNat = (stackArg s 3).toNat
  hqil : (stackArg s 11).toNat = (stackArg s 3).toNat
  hdql : (stackArg s 9).toNat = (stackArg s 5).toNat
  hsl : 16 * (s.gpr .rcx).toNat + 32 ≤ (stackArg s 13).toNat
  hprl : (stackArg s 15).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 3).toNat
    (stackArg s 5).toNat

theorem preFPc_of {s : State} (h : chkPcContract.pre s) : PreFPc s := by
  simp only [chkPcContract] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOi dOp dOq dOdp dOdq dOqi dOpre dOs dOa dns des dis dps dqs ddps ddqs
    dqis dpres dsa dRo _ _ _ _ _ _ _ _ _ dRs _ dKo dKn dKe dKi dKp dKq dKdp dKdq dKqi dKpre dKs dKa wO wN wE wI wP
    wQ wDp wDq wQi wS wPre _ob1 hsi hil L1 L2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsl
  obtain ⟨k1, k2⟩ := _ob1
  have hprl := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOpre, dOs, dOa, dns, des, dis, dps, dqs,
    ddps, ddqs, dqis, dpres, dsa, dRo, dRs, dKo, dKn, dKe, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKpre, dKs, dKa, wO, wN,
    wE, wI, wP, wQ, wDp, wDq, wQi, wS, wPre, k1, k2, hsi, hil, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl,
    hprl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fbP (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, the caller's `out` and the working space:
all the function and its calls may write. -/
def stkRP (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, stackBytesPc⟩

theorem fbP_eq (s : State) : fbP s = off (s.gpr .rsp - BitVec.ofNat 64 stackBytesPc) 16 :=
  Offset.sub_ofNat_eq _ (by decide)

/-- Bytes of the frame are in the stack the function uses. -/
theorem frameP_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fbP s) d, n⟩ (stkRP s) := by
  rw [fbP_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold stackBytesPc; omega)

/-- The return addresses of a call from the frame and of its calls. -/
theorem ret2P_sub (s : State) : Region.Sub (below (fbP s) 16) (stkRP s) := by
  rw [show below (fbP s) 16 = ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, 16⟩ by
    simp only [below, fbP, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
  exact Region.sub_prefix (by decide)

/-- The return address of a call from the frame. -/
theorem retP_sub (s : State) : Region.Sub (below (fbP s) 8) (stkRP s) := by
  rw [show below (fbP s) 8 = ⟨s.gpr .rsp - BitVec.ofNat 64 (frameBytes + 8), 8⟩ by
    simp only [below, fbP, BitVec.sub_sub, ← BitVec.ofNat_add]]
  exact Offset.sub_below _ (by decide) (by decide)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outsideP_frame (s : State) {x : Addr} (hx : ¬ (stkRP s).Contains x 1) :
    frameBytes ≤ ofs (fbP s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fbP s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega
  have := frameP_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- Between the calls, from the entry state `s`: in the frame, with `out`,
`n`, `n_len`, `e` and `e_len` in their slots, memory changed only where the
function may write. -/
structure EnvP (s t : State) : Prop where
  rsp : t.gpr .rsp = fbP s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fbP s, frameBytes⟩ :: s.wr
  mem : Frame [stkRP s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fbP s) oOut = s.gpr .rdi
  sN : word t.mem (fbP s) oN = s.gpr .rdx
  sK : word t.mem (fbP s) oK = s.gpr .rcx
  sE : word t.mem (fbP s) oE = s.gpr .r8
  sEl : word t.mem (fbP s) oEl = s.gpr .r9

theorem EnvP.scr {s t : State} (h : EnvP s t) (hp : PreFPc s) : Scr t (fbP s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by
    have := hp.sp1; simp only [fbP, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytesPc at *
    omega)

/-- A buffer of the caller that the function does not write. -/
theorem EnvP.bytes {s t : State} (h : EnvP s t) {p : Addr} {len : Nat} (hk : (stkRP s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.mem.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem EnvP.arg {s t : State} (h : EnvP s t) (hp : PreFPc s) {j : Nat} (hj : j < 16) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 128⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem stackArgAddr_fbP (s : State) (j : Nat) : stackArgAddr s j = off (fbP s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem fbP_toNat {s : State} (hp : PreFPc s) : (fbP s).toNat + frameBytes + 8 + 128 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [fbP, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytesPc at *; omega

/-- Memory changed only in the frame turns into `EnvP`'s. -/
theorem frameP_of_outside {s : State} {m : Mem} (h : Outside (fbP s) 0 frameBytes s.mem m) :
    Frame [stkRP s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outsideP_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem argP_outside {s : State} (hp : PreFPc s) {m : Mem} (h : Outside (fbP s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 16) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fbP_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fbP]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-! ## The CRT's arguments -/

def slotStoresP : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oN) .rdx, .store (sp oK) .rcx, .store (sp oE) .r8, .store (sp oEl) .r9]

def copyArgP (j : Nat) : List Instr := [.mov .rax (.mem (arg (j + 2))), .store (sp (8 * j)) .rax]

def crtRegsP : List Instr :=
  lea .rdi oM ++ [.mov .rsi (.reg .rcx), .mov .r8 (.mem (arg 0)), .mov .r9 (.reg .rcx)]

theorem crtArgsP_eq : crtArgs = slotStoresP ++ ((List.range 14).flatMap copyArgP ++ crtRegsP) := rfl

theorem slotStoresP_ok {s t : State} (hsp : t.gpr .rsp = fbP s) (hs : Scr t (fbP s) frameBytes) :
    WP isa (.block slotStoresP) t fun t' => t'.mem =
      ((((t.mem.writeW (off (fbP s) oOut) (t.gpr .rdi)).writeW (off (fbP s) oN) (t.gpr .rdx)).writeW
        (off (fbP s) oK) (t.gpr .rcx)).writeW (off (fbP s) oE) (t.gpr .r8)).writeW (off (fbP s) oEl) (t.gpr .r9) ∧
      Keep [] t t' :=
  WP.keep [] (by
    xrun [slotStoresP, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oN) (by decide),
      hs.st (d := oK) (by decide), hs.st (d := oE) (by decide), hs.st (d := oEl) (by decide)]) rfl

/-- Stack argument `j + 2` to the frame's word `j`. -/
theorem copyArgP_ok {s t : State} (hp : PreFPc s) (hsp : t.gpr .rsp = fbP s) (hs : Scr t (fbP s) frameBytes)
    (hrd : t.rd = s.rd) (ho : Outside (fbP s) 0 frameBytes s.mem t.mem) {j : Nat} (hj : j < 14) :
    WP isa (.block (copyArgP j)) t fun t' => t'.mem = t.mem.writeW (off (fbP s) (8 * j)) (stackArg s (j + 2)) ∧
      Keep [.rax] t t' := by
  have ha : InRegions (t.rd ++ t.wr) (stackArgAddr s (j + 2)) 8 :=
    ⟨⟨stackArgAddr s 0, 128⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
      by rw [stackArgAddr_eq s (j + 2)]; exact Offset.contains_base _ (by omega) (by omega)⟩
  exact WP.keep [.rax] (by
    xrun [copyArgP, ea_argP hsp, ea_sp, hsp, ha, argP_outside hp ho (show j + 2 < 16 by omega),
      hs.st (d := 8 * j) (by unfold frameBytes; omega)]) rfl

/-- The first `n` copies. -/
theorem copiesP_ok {s : State} (hp : PreFPc s) : ∀ (n : Nat), n ≤ 14 → ∀ (t : State), t.gpr .rsp = fbP s →
    Scr t (fbP s) frameBytes → t.rd = s.rd → Outside (fbP s) 0 frameBytes s.mem t.mem →
    WP isa (.block ((List.range n).flatMap copyArgP)) t fun t' => Outside (fbP s) 0 frameBytes s.mem t'.mem ∧
      (∀ i < n, word t'.mem (fbP s) (8 * i) = stackArg s (i + 2)) ∧
      (∀ d, 8 * n ≤ d → d + 8 ≤ frameBytes → word t'.mem (fbP s) d = word t.mem (fbP s) d) ∧ Keep [.rax] t t'
  | 0, _, t, _, _, _, ho => WP.block_nil ⟨ho, fun _ h => absurd h (by omega), fun _ _ _ => rfl, Keep.refl _ _⟩
  | n + 1, hn, t, hsp, hs, hrd, ho => by
    have hF := fbP_toNat hp
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copiesP_ok hp n (by omega) t hsp hs hrd ho) fun t₁ ⟨ho₁, hw₁, hk₁, k₁⟩ => ?_
    refine WP.mono (copyArgP_ok hp ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) (k₁.2.1.trans hrd) ho₁
      (show n < 14 by omega)) fun t' ⟨hm, k'⟩ => ⟨?_, fun i hi => ?_, fun d hd hd' => ?_,
        (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      exact fun x hx => (writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega)).trans
        (ho₁ x hx)
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(writeW_outside t₁.mem (fbP s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
          (.inl (by omega)) (by unfold frameBytes at *; omega)]
        exact hw₁ i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm, (writeW_outside t₁.mem (fbP s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
        (.inr (by omega)) (by unfold frameBytes at *; omega)]
      exact hk₁ d (by omega) hd'

theorem allocStateP_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fbP s else s.gpr r := rfl

/-- The frame's push, and the CRT's arguments: `EnvP`, the CRT's stack
arguments in the frame, and its arguments in registers. -/
theorem crtArgsP_ok {s : State} (hp : PreFPc s) :
    WP isa (.block crtArgs) (allocState frameBytes s) fun t => EnvP s t ∧
      Outside (fbP s) 0 frameBytes s.mem t.mem ∧ (∀ i < 14, word t.mem (fbP s) (8 * i) = stackArg s (i + 2)) ∧
      t.gpr .rdi = off (fbP s) oM ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx := by
  have hF := fbP_toNat hp
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fbP s := rfl
  have hs : Scr A (fbP s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  rw [crtArgsP_eq, WP.block_append_iff]
  refine WP.mono (slotStoresP_ok hsp hs) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fbP s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ ofs (fbP s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    simp only [oOut, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega)]
    rfl
  have hslots : word t₁.mem (fbP s) oOut = s.gpr .rdi ∧ word t₁.mem (fbP s) oN = s.gpr .rdx ∧
      word t₁.mem (fbP s) oK = s.gpr .rcx ∧ word t₁.mem (fbP s) oE = s.gpr .r8 ∧ word t₁.mem (fbP s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oN, oK, oE, oEl]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (copiesP_ok hp 14 (le_refl _) t₁ ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) k₁.2.1 ho₁)
    fun t₂ ⟨ho₂, hw₂, hk₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hrd₂ : InRegions (t₂.rd ++ t₂.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 128⟩, List.mem_append_left _ (by
      rw [k12.2.1, show A.rd = s.rd from rfl, hp.hrd]
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))))))),
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.mono (WP.keep [.rdi, .rsi, .r8, .r9] (Q := fun t => t.gpr .rdi = off (fbP s) oM ∧
      t.gpr .rsi = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx ∧ t.mem = t₂.mem) (by
    xrun [crtRegsP, lea, List.cons_append, List.nil_append, sx_ofNat (show oM < 2 ^ 31 by decide), arg, ea_sp, hsp,
      show fbP s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fbP s 0).symm, k12.gpr (show Reg.rsp ∉ [] ++ [Reg.rax] by decide),
      k12.gpr (show Reg.rcx ∉ [] ++ [Reg.rax] by decide), hrd₂, argP_outside hp ho₂ (show 0 < 16 by decide)]
    exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨hdi, hsi, h8, h9, hm⟩, k⟩ => ?_
  have k' := k12.trans k
  have hw : ∀ d, 112 ≤ d → d + 8 ≤ frameBytes → word t.mem (fbP s) d = word t₁.mem (fbP s) d := fun d hd hd' => by
    rw [hm]; exact hk₂ d (by omega) hd'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hslots
  refine ⟨⟨(k'.gpr (by decide)).trans hsp, k'.2.1, k'.2.2, frameP_of_outside (hm ▸ ho₂),
      (hw _ (by decide) (by decide)).trans h1, (hw _ (by decide) (by decide)).trans h2,
      (hw _ (by decide) (by decide)).trans h3, (hw _ (by decide) (by decide)).trans h4,
      (hw _ (by decide) (by decide)).trans h5⟩, hm ▸ ho₂, fun i hi => hm ▸ hw₂ i hi, hdi, hsi,
    (k'.gpr (by decide)).trans rfl, (k'.gpr (by decide)).trans rfl, h8, h9⟩

end VG.Proof.Rsa.X86_64
