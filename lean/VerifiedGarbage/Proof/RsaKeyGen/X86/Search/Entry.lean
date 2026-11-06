module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Data
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Search
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Data
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Search
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Rc2.PairMem

/-! # The search's push and entry (i686)

The push of the four callee-saved registers, which changes only the
search's stack and saves them (`push_base`); the arguments, which every loop
state reads at the same addresses (`SearchBase.arg_*`); and the entry, which
starts the loop with nothing consumed (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit)

/-- A block's run, with what it keeps: the registers but `rs`, the
regions and the statics. -/
theorem WP.blockKeep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hw : writesOnly rs (.block is) = true) :
    WP isa (.block is) s fun t => Q t ∧ Keep rs s t ∧ t.syms = s.syms :=
  WP.mono_syms (WP.keep rs h hw) fun _ ⟨q, k⟩ sy => ⟨q, k, sy⟩

namespace SearchInput

variable {p : SearchPublic} {o : State}

theorem len_valid (h : SearchInput p o) : 32 ≤ p.len ∧ p.len ≤ 512 := by
  have hv := h.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv; exact ⟨hv.1, hv.2.1⟩

theorem remaining_le (h : SearchInput p o) : p.remaining ≤ 32768 := by
  have hr := h.facts.remaining
  have hv := h.len_valid
  unfold primeLimit at hr
  split at hr <;> omega

end SearchInput

/-- The push changes only the search's stack. -/
theorem push_frame {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 216 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  refine (pushed_frame (rs := pushRegs) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)).sub
    fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨below (o.gpr .esp) 216, by simp [changes], below_sub (by decide) hroom⟩

theorem push_saved {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 216 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  have hn : 4 * pushRegs.length ≤ (o.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega
  have hS : p.S1 = (pushed pushRegs o).gpr .esp := by rw [SearchPublic.S1, h.sp_eq, pushed_esp]; rfl
  have w (i : Nat) (hi : i < 4) := pushed_word (rs := pushRegs) (s := o) (by decide) hn hi
  rw [hS]
  exact ⟨w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide)⟩

theorem push_base {p : SearchPublic} {o : State} (h : SearchInput p o) : SearchBase p o (pushed pushRegs o) where
  input := h
  rd := pushed_rd _ _
  wr := by rw [pushed_wr, h.sp_eq]; rfl
  syms := pushRegs_syms _ _
  sp := by rw [pushed_esp, SearchPublic.S1, h.sp_eq]; rfl
  saved := push_saved h
  frame := push_frame h

namespace SearchBase

variable {p : SearchPublic} {o s : State}

/-- A state of the loop, through code that keeps `esp`, the regions, the
statics and the memory but in what the search may write. -/
theorem keep (hb : SearchBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hs : Saved t.mem p.S1 o) (hf : Frame (changes o) s.mem t.mem) :
    SearchBase p o t :=
  ⟨hb.input, k.2.1.trans hb.rd, k.2.2.trans hb.wr, sy.trans hb.syms, (k.gpr hrs).trans hb.sp, hs,
    hb.frame.trans hf⟩

/-- The same, for code that keeps memory. -/
theorem step (hb : SearchBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hm : t.mem = s.mem) : SearchBase p o t :=
  hb.keep k hrs sy (by rw [hm]; exact hb.saved) (by rw [hm]; exact Frame.refl _ _)

/-- The address of argument `i`, at displacement `d = 20 + 4 i` from `esp`. -/
theorem arg_ea (hb : SearchBase p o s) {i d : Nat} (hd : 20 + 4 * i = d) :
    (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = argAddr o i := by
  rw [hb.sp, SearchPublic.S1, hb.input.sp_eq, ← hd]
  unfold argAddr
  congr 1
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_in (hb : SearchBase p o s) {i : Nat} (hi : i < 12) : InRegions (s.rd ++ s.wr) (argAddr o i) 4 := by
  have A := hb.input.abi
  have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  refine ⟨aR o, ?_, ?_⟩
  · rw [hb.rd, hb.wr, A.wr]; simp
  · rw [ai, show aR o = ⟨argAddr o 0, 48⟩ from rfl, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_val (hb : SearchBase p o s) {i : Nat} (hi : i < 12) : s.mem.readW (argAddr o i) 32 = arg o i :=
  hb.input.arg_frame hb.frame hi

end SearchBase

theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

theorem param_eq (extra i : Nat) : param extra i = at_ .esp (4 + 4 * i + 4 * (pushWords + extra)) := rfl

theorem entry_ok {p : SearchPublic} {o : State} (h : SearchInput p o) :
    WP isa (.block entry) (pushed pushRegs o) (SearchLive p o 0 p.remaining) := by
  have hb := push_base h
  have A := h.abi
  have hst : p.stp = arg o 11 := by rw [← h.2]; rfl
  have r11 := hb.arg_in (i := 11) (by decide)
  have v11 := hb.arg_val (i := 11) (by decide)
  have e11 := hb.arg_ea (i := 11) (d := 64) rfl
  have cs : (sR o).Contains ((arg o 11).setWidth 64) 4 := by
    simpa using Offset.contains_base ((arg o 11).setWidth 64) (d := 0) (n := 4) (k := 32) (by decide) (by decide)
  have rs : InRegions ((pushed pushRegs o).rd ++ (pushed pushRegs o).wr) ((arg o 11).setWidth 64) 4 := by
    refine ⟨sR o, ?_, cs⟩
    rw [hb.rd, hb.wr, A.wr]; simp
  have vs : (pushed pushRegs o).mem.readW ((arg o 11).setWidth 64) 32 = BitVec.ofNat 32 p.remaining := by
    have hd : (sR o).Disjoint (below (o.gpr .esp) 16) :=
      A.lowS.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
    have e := (pushed_frame (rs := pushRegs) (s := o) (by decide)
      (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega)).readW (r := sR o)
      (a := (arg o 11).setWidth 64) (w := 32) cs (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact hd) (by decide)
    rw [e]
    have hw : o.mem.readW ((arg o 11).setWidth 64) 64 = BitVec.ofNat 64 p.remaining := by
      rw [← h.2]; change o.mem.readW (sR o).base 64 = BitVec.ofNat 64 (searchRemaining o)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact low_half hw
  have e0 : (arg o 11 + BitVec.ofNat 32 0).setWidth 64 = (arg o 11).setWidth 64 := by rw [BitVec.add_zero]
  refine WP.mono (WP.blockKeep [.eax, .ebx, .ebp, .esi, .edi] (Q := fun t =>
      t.gpr .esi = 0 ∧ t.gpr .edi = BitVec.ofNat 32 p.remaining ∧ t.gpr .ebx = 4 ∧
      t.mem = (pushed pushRegs o).mem) ?_ (by rfl)) fun t ⟨⟨hsi, hdi, hbx, hm⟩, k, sy⟩ => ?_
  · simp only [entry, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, e11, r11, v11, e0, rs, vs]
  · exact ⟨hb.step k (by decide) sy hm, Nat.zero_le _, Nat.le_refl _, hsi, hdi, hbx⟩

end VG.Proof.RsaKeyGen.X86.Search
