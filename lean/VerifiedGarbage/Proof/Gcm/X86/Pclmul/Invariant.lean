import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Const
import VerifiedGarbage.Proof.Gcm.X86.GhashCT

section

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd
open VG.Impl.Gcm.X86.Pclmul (at_ argOp)
open VG.Proof.Gcm.X86 (GPre aR)

theorem args_in {s : State} (hp : GPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  refine ⟨aR s, by simp only [hp.rd, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_true, true_or], ?_⟩
  exact Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20)
    hp.fSp (by decide) (by omega) (by omega) (by decide)

theorem ea_arg (s : State) (i : Nat) : s.ea (argOp i) = argAddr s i := rfl

theorem movArg_exec {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : i < 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hsp]
  simp only [exec, readSrc, State.load32, he, hrd, hwr, args_in hp hi,
    ite_true, hm, Option.map_some, arg]

/-- Load a big-endian GHASH block, retaining every general-purpose register. -/
theorem ldrev_ok (r : XReg) (b : Reg) (d : Nat) (s : State) (hr : r ≠ .xmm0)
    (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b d)) 16) :
    WP isa (.block [.movdquLoad r (at_ b d), .xop (.bin .pshufb r .xmm0)]) s fun s' =>
      s'.xmm r = Spec.Gcm.blockAt s.mem (s.ea (at_ b d)) ∧ Only [r] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, XOp.exec, State.load128, hin, xmm_setXmm, Ne.symm hr,
    h0, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun a ha => ?_⟩
  · rw [VG.Proof.Gcm.X86.blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [xmm_setXmm, ha, ite_false]

end VG.Proof.Gcm.X86.Pclmul

end

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- Every instruction before the final Y store retains memory, regions and
all cdecl callee-saved registers. -/
structure Env (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem Env.refl (s : State) : Env s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Env.sp {s₀ s : State} (h : Env s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Env.of_setup {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : SetupFrame rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr, fun r hr => by
    have hn : r ≠ .eax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hf.gpr r hn).trans (h.saved r hr)⟩

theorem Env.of_only {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : Only rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (congrFun hf.gpr r).trans (h.saved r hr)⟩

theorem Env.setReg {s₀ s : State} (h : Env s₀ s) (d : Reg) (v : BitVec 32)
    (hd : d ∉ calleeSaved) : Env s₀ (s.setReg d v) :=
  ⟨(mem_setReg s d v).trans h.mem, (rd_setReg s d v).trans h.rd,
    (wr_setReg s d v).trans h.wr, fun r hr => by
    rw [gpr_setReg_of_ne s v (show r ≠ d from fun heq => hd (heq ▸ hr))]
    exact h.saved r hr⟩

abbrev H (s₀ : State) : Block := blockAt s₀.mem ((hP s₀).setWidth 64)
abbrev Y (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H s₀) (blockAt s₀.mem ((yP s₀).setWidth 64))
    (blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- The accumulator after i blocks and public remaining count/data pointer. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  env : Env s₀ s
  le : i ≤ nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  out : s.gpr .ecx = yP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  hash : x * φ (s.xmm .xmm3) = φ (H s₀)
  acc : s.xmm .xmm2 = Y s₀ i

end VG.Proof.Gcm.X86.Pclmul
