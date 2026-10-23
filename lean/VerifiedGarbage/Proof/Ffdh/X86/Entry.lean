module

public import VerifiedGarbage.Proof.Ffdh.X86.Frame
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.X86.Words

/-!
# FFDH on i686: entry and return around the frame of the synthetic arguments

`wrap_ok`: `wrap a body` saves the callee-saved registers in the working
space's header, allocates the frame of the synthetic arguments and fills it,
so that `body` runs from a state of private CRT's operations (`In`), and
restores the registers: what `body` leaves in memory and `eax`, with the
caller's ABI preserved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Impl.Ffdh.X86 (Args argsFrame fill entry wrap)
open VG.Proof.Dsa.X86 (argumentPointer stackAddress stackValue StackArgument)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The working space's base, its bytes, and the modulus's length. -/
abbrev wsBase (a : Args) (s : State) : Addr := argumentPointer s a.ws
abbrev wsSize (a : Args) (s : State) : Nat := (arg s (a.ws + 1)).toNat * 8
abbrev pLenOf (a : Args) (s : State) : Nat := (arg s a.plen).toNat

/-- The frame of the synthetic arguments, below the entry's `esp`. -/
abbrev frameAt (s : State) : Addr := (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64

/-- What `wrap a body` needs of the entry state, a function of `n` arguments, which it may overwrite. -/
structure WrapABI (a : Args) (n : Nat) (s : State) : Prop where
  below : Below a n
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  argsIn : (⟨argAddr s 0, 4 * n⟩ : Region) ∈ s.wr
  wsIn : (⟨wsBase a s, wsSize a s⟩ : Region) ∈ s.wr
  scratchArgs : Region.Disjoint ⟨wsBase a s, wsSize a s⟩ ⟨argAddr s 0, 4 * n⟩
  retScratch : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsBase a s, wsSize a s⟩
  belowScratch : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨wsBase a s, wsSize a s⟩
  scratchBound : (arg s a.ws).toNat + wsSize a s ≤ 2 ^ 32
  lower : 64 ≤ pLenOf a s
  upper : pLenOf a s ≤ 1024
  scratchLength : Spec.Rsa.scratchWords (pLenOf a s) ≤ (arg s (a.ws + 1)).toNat

section
variable {a : Args} {n : Nat} {s : State}

theorem WrapABI.argument (A : WrapABI a n s) {i : Nat} (hi : i < n) : StackArgument s (wsBase a s) (wsSize a s) i :=
  VG.Proof.Dsa.X86.stackArgument_of (count := n) (by have := A.stackBound; omega) hi
    (List.mem_append_right _ A.argsIn) A.scratchArgs.symm

theorem WrapABI.need (A : WrapABI a n s) : CrtRt.need (pLenOf a s) ≤ wsSize a s := by
  have := A.scratchLength
  have := A.lower
  have := A.upper
  simp only [CrtRt.need, CrtRt.st, CrtRt.bc, CrtRt.mw, Spec.Rsa.modulusWords, Impl.Bignum.X86.CrtRt.numBase,
    Spec.Rsa.scratchWords, wsSize] at *
  omega

theorem WrapABI.base_toNat (_ : WrapABI a n s) : (wsBase a s).toNat = (arg s a.ws).toNat := by
  simp only [wsBase, argumentPointer, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s a.ws).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

/-- `entry a`: `edi` the working space, the callee-saved registers saved in its header. -/
theorem entry_ok (A : WrapABI a n s) :
    WP isa (.block (entry a)) s fun t =>
      Scr t (wsBase a s) (wsSize a s) ∧ Saved t.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (wsBase a s) 0 (wsSize a s) s.mem t.mem := by
  have hz : 48 ≤ wsSize a s := by have := A.need; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega
  have hb := A.base_toNat
  have read := (A.argument (i := a.ws) (by have := A.below.ws; omega)).readSrc
  have stk : StkOk (s.gpr .esp) (wsBase a s) (wsSize a s) :=
    VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 172) A.stackLow (by rw [hb]; exact A.scratchBound)
      (by omega) A.belowScratch
  unfold entry
  rw [show Impl.Bignum.X86.CrtRt.save = Impl.Bignum.X86.Crt.save from rfl]
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (Crt.entrySave_ok (base := wsBase a s) (size := wsSize a s)
    (by rw [U.gpr]; rfl) (by rw [U.gpr]; exact A.scratchBound) hz (by rw [U.wr]; exact A.wsIn))
    fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; rfl
    · rw [T.wr, Wr, U.wr]; exact A.wsIn
    · rw [hb]; exact A.scratchBound
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [Impl.Bignum.X86.Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro x hx
    rw [T.mem]
    have H : ¬ InRegions [⟨wsBase a s, wsSize a s⟩] x 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs (wsBase a s) x + 1 ≤ wsSize a s)
      omega
    exact (F x (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem x)

/-- The entry's argument `j` read through the frame of the synthetic arguments. -/
theorem argAt_frame (A : WrapABI a n s) {s₁ : State} (K : Keeps [.eax, .edi] s s₁)
    (O : Outside (wsBase a s) 0 (wsSize a s) s.mem s₁.mem) {j : Nat} (hj : j < n) :
    readSrc (allocFrame argsFrame s₁) (.mem (argAt 19 j)) = some (arg s j) ∧
      Region.Disjoint ⟨(allocFrame argsFrame s₁).ea (argAt 19 j), 4⟩ ⟨frameAt s, argsFrame⟩ := by
  have SA := A.argument hj
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have low := A.stackLow
  have top := A.stackBound
  have hE := (s.gpr .esp).isLt
  have ea : (allocFrame argsFrame s₁).ea (argAt 19 j) = stackAddress s j := by
    simp only [State.ea, argAt, at_, allocFrame_esp, sp, stackAddress, addr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, argsFrame]
    omega
  have SE : stackAddress s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) := addr_eq (by omega)
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  refine ⟨?_, ?_⟩
  · simp only [readSrc, State.load32, ea, allocFrame_mem, allocFrame_rd, allocFrame_wr]
    have rd : InRegions (s₁.rd ++ ⟨(s₁.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64, argsFrame⟩ :: s₁.wr)
        (stackAddress s j) 4 := by
      obtain ⟨r, hr, hc⟩ := SA.read
      refine ⟨r, ?_, hc⟩
      rw [K.2.1, K.2.2] at *
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    rw [ite_eq_left_of_eq_true _ _ (eq_true rd)]
    have F := VG.Proof.Bignum.outside_frame O (by have := A.scratchBound; have := A.base_toNat; omega)
    simp only [off, BitVec.add_zero] at F
    exact congrArg some (F.readW (r := ⟨stackAddress s j, 4⟩) (Region.contains_self _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact SA.apart) (by decide))
  · rw [ea, SE, FA]
    exact Offset.disjoint_below _ (by omega)

/-- The state after the frame of the synthetic arguments is filled: private CRT's operations' inputs
`In`, from the entry state `s` and the state `s₁` after `entry`. -/
theorem frameIn_ok (A : WrapABI a n s) {s₁ : State} (S : Scr s₁ (wsBase a s) (wsSize a s))
    (K : Keeps [.eax, .edi] s s₁) (O : Outside (wsBase a s) 0 (wsSize a s) s.mem s₁.mem)
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame → f.rd = s.rd →
      f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem →
      Frame [⟨frameAt s, argsFrame⟩] s₁.mem f.mem →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esp → f.gpr r = s₁.gpr r) → WP isa (.block is) f Q) :
    WP isa (.block (fill a ++ is)) (allocFrame argsFrame s₁) Q := by
  have sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have low := A.stackLow
  have top := A.stackBound
  have hE := (s.gpr .esp).isLt
  have hb := A.base_toNat
  have bd := A.scratchBound
  have nd := A.need
  have hz : 48 ≤ wsSize a s := by
    have := nd; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega
  have lo := A.lower
  have hi := A.upper
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have t0esp : (allocFrame argsFrame s₁).gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := by
    rw [allocFrame_esp, sp]
  have t0P : ((allocFrame argsFrame s₁).gpr .esp).setWidth 64 = frameAt s := by rw [t0esp]
  have espN : (s.gpr .esp - BitVec.ofNat 32 argsFrame).toNat = (s.gpr .esp).toNat - 76 :=
    VG.X86.sub_toNat (by omega)
  refine fill_ok A.below t0P (by rw [t0esp, espN]; omega)
    (by rw [allocFrame_wr, sp]; exact List.mem_cons_self ..)
    (fun j hj => (argAt_frame A K O hj).1) (fun j hj => (argAt_frame A K O hj).2) 18 (Nat.le_refl _)
    fun f Kf Ff Sf => ?_
  -- The frame lies below the entry's `esp`, within the 172 bytes apart from the working space.
  have frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have frameWs : Region.Disjoint ⟨frameAt s, argsFrame⟩ ⟨wsBase a s, wsSize a s⟩ :=
    A.belowScratch.sub_left frameSub
  have espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := by rw [Kf.1 _ (by decide), t0esp]
  have espfN : (f.gpr .esp).toNat = (s.gpr .esp).toNat - 76 := by rw [espf, espN]
  have edif : f.gpr .edi = s₁.gpr .edi := by rw [Kf.1 _ (by decide), allocFrame_gpr _ _ (by decide)]
  have rdf : f.rd = s.rd := by rw [Kf.2.1, allocFrame_rd, K.2.1]
  have wrf : f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr := by rw [Kf.2.2, allocFrame_wr, sp, K.2.2]
  have belowf : Region.Disjoint (below (f.gpr .esp) 96) ⟨wsBase a s, wsSize a s⟩ := by
    refine A.belowScratch.sub_left ?_
    simp only [below]
    rw [espf, VG.X86.Taint.sub_setWidth (by rw [espN]; omega),
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  have stackF : ∀ i < 18, CallArgument f (wsBase a s) (wsSize a s) i (synth a (arg s) i) := by
    intro i hi
    have SAd : stackAddress f i = slotAddr (frameAt s) i := by
      rw [stackAddress, espf, addr_eq (by rw [espN]; omega)]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [SAd, rdf, wrf]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ (by omega) (by omega)⟩
    · rw [SAd]; exact frameWs.sub_left (Offset.sub_base _ (by omega))
    · show f.mem.readW (stackAddress f i) 32 = _
      rw [SAd]; exact Sf i hi
  have stk : StkOk (f.gpr .esp) (wsBase a s) (wsSize a s) := by
    refine VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) (by rw [espfN]; omega) (by rw [hb]; exact bd)
      (by omega) ?_
    have := belowf
    simp only [below] at this
    rwa [VG.X86.Taint.sub_setWidth (by rw [espfN]; omega)] at this
  have Ft : Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem := by
    have F₁ := VG.Proof.Bignum.outside_frame O (by omega)
    simp only [off, BitVec.add_zero] at F₁
    exact (F₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).trans
      (by rw [← allocFrame_mem argsFrame s₁]
          exact Ff.mono fun r hr => by
            rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine k f ⟨⟨by rw [edif]; exact S.edi, by rw [wrf]; exact List.mem_cons_of_mem _ (by rw [← K.2.2]; exact S.wr),
      S.nowrap, stk⟩, A.lower, A.upper, stackF, ?_, ⟨by rw [espfN]; omega, belowf⟩, by rw [espfN]; omega, A.need,
      hb.symm, rfl, by rw [rdf, wrf]; exact hx⟩ espf rdf wrf Ft (by rw [← allocFrame_mem argsFrame s₁]; exact Ff) ?_
  · show arg s a.plen = _
    simp only [pLenOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3
    rw [Kf.1 r (by simp [h1, h2]), allocFrame_gpr _ _ h3]

/-- The saved registers' words, within the working space's header. -/
theorem saved_keep {base : Addr} {m m' : Mem} {g : Reg → BitVec 32} {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨off base 32, 16⟩ r)
    (S : Saved m (off base) g Impl.Bignum.X86.Crt.savedRegisters) :
    Saved m' (off base) g Impl.Bignum.X86.Crt.savedRegisters := by
  intro p hp
  have B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
    simp only [Impl.Bignum.X86.Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  exact (F.readW (r := ⟨off base 32, 16⟩) (Offset.contains base B.1 (by omega) (by decide)) hd (by decide)).trans
    (S p hp)

/-- A range of `fR`, past the saved registers' words. -/
theorem fR_saved {base : Addr} {len size : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (hf : CrtRt.need len ≤ size) :
    ∀ p ∈ fR len, Region.Disjoint ⟨off base 32, 16⟩ ⟨off base p.1, p.2⟩ := by
  have : 48 ≤ CrtRt.need len := by simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase]; omega
  intro p hp
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Offset.disjoint base (d := 32) (n := 16) (e := 0) (k := 32) (.inr (Nat.le_refl _)) (by decide) (by decide)
  · exact Offset.disjoint base (d := 32) (n := 16) (e := 48) (k := CrtRt.need len - 48) (.inl (Nat.le_refl _))
      (by decide) (by omega)

/-- `wrap a body`: what `body` leaves in memory and `eax`, run from the state `In` of private CRT's
operations, with the ABI preserved and the statics where they were. `body` may also write the regions
`Out`, apart from the return address and the working space. -/
theorem wrap_syms_ok (A : WrapABI a n s) {body : Prog isa} (hsp : NoSp (.seq (.block (fill a)) body))
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {Out : List Region} (outRet : ∀ r ∈ Out, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    (outWs : ∀ r ∈ Out, Region.Disjoint ⟨wsBase a s, wsSize a s⟩ r) {P : Mem → BitVec 32 → Prop}
    (hb : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem → f.syms = s.syms →
      WP isa body f fun t => P t.mem (t.gpr .eax) ∧
        Frame (Out ++ CrtRt.frameR (wsBase a s) (f.gpr .esp) (fR (pLenOf a s))) f.mem t.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t) :
    WP isa (wrap a body) s fun u => P u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have low := A.stackLow
  have top := A.stackBound
  have hE := (s.gpr .esp).isLt
  have hb' := A.base_toNat
  have bd := A.scratchBound
  have nd := A.need
  have hz : 48 ≤ wsSize a s := by
    have := nd; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  unfold wrap
  refine WP.seq (WP.mono_syms (entry_ok A) fun s₁ ⟨S, Sv, K, O⟩ sy₁ => ?_)
  have sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  -- The saved registers and the return address, kept by what the frame changes.
  have retWs := A.retScratch
  have retFrame : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨frameAt s, argsFrame⟩ := by
    rw [FA]; exact Offset.base_disjoint_below _ (by omega)
  let R : State → Prop := fun u => P u.mem (u.gpr .eax) ∧ Scr u (wsBase a s) (wsSize a s) ∧
    Saved u.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters ∧ u.gpr .esp = s.gpr .esp ∧
    u.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  refine WP.seq (WP.mono (Q := R) (WP.frameAlloc (bytes := argsFrame) (by decide) (by decide) (by decide)
    (by rw [sp]; omega) hsp ?_) fun s₂ R₂ => ?_)
  · rw [show Impl.Ffdh.X86.fill a = Impl.Ffdh.X86.fill a ++ [] from (List.append_nil _).symm]
    refine WP.seq (WP.mono_syms (frameIn_ok A S K O hx (Q := fun f =>
        In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f ∧
        f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame ∧ f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr ∧
        Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem ∧
        Frame [⟨frameAt s, argsFrame⟩] s₁.mem f.mem ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esp → f.gpr r = s₁.gpr r))
      fun f I espf _ wrf Ft Ff₁ regs => WP.block_nil ⟨I, espf, wrf, Ft, Ff₁, regs⟩)
      fun f ⟨I, espf, wrf, Ft, Ff₁, regs⟩ syf => ?_)
    refine WP.mono (hb f I espf Ft (syf.trans sy₁)) fun t ⟨Pt, Fb, Kt⟩ => ?_
    have espt : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := (Kt.1 _ (by decide)).trans espf
    have ediT : t.gpr .edi = s₁.gpr .edi := (Kt.1 _ (by decide)).trans (regs _ (by decide) (by decide) (by decide))
    have espN : (s.gpr .esp - BitVec.ofNat 32 argsFrame).toNat = (s.gpr .esp).toNat - 76 :=
      VG.X86.sub_toNat (by omega)
    have belowRet : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ (below (f.gpr .esp) 96) := by
      simp only [below]
      rw [espf, VG.X86.Taint.sub_setWidth (by rw [espN]; omega),
        show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
        ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
      exact (Offset.base_disjoint_below _ (n := 172) (k := 4) (by decide)).sub_right (Region.sub_prefix (by decide))
    have bnd : (wsBase a s).toNat + wsSize a s ≤ 2 ^ 32 := by rw [hb']; exact bd
    have savedSub : Region.Sub ⟨off (wsBase a s) 32, 16⟩ ⟨wsBase a s, wsSize a s⟩ :=
      Offset.sub_base _ (d := 32) (n := 16) (by omega)
    have belowWs : Region.Disjoint ⟨off (wsBase a s) 32, 16⟩ (below (f.gpr .esp) 96) :=
      (I.room.apart.sub_right savedSub).symm
    have frameWs16 : Region.Disjoint ⟨off (wsBase a s) 32, 16⟩ ⟨frameAt s, argsFrame⟩ := by
      have frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
        rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
      exact ((A.belowScratch.sub_left frameSub).sub_right savedSub).symm
    have Sv₁ : Saved f.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters :=
      saved_keep Ff₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact frameWs16) Sv
    have Svt : Saved t.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters := by
      refine saved_keep Fb (fun r hr => ?_) Sv₁
      rcases List.mem_append.mp hr with hr | hr
      · exact ((outWs r hr).sub_left savedSub)
      · rw [CrtRt.frameR, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨p, hp, rfl⟩
        · exact belowWs
        · exact fR_saved bnd nd p hp
    have F₀ := VG.Proof.Bignum.outside_frame O (by omega)
    simp only [off, BitVec.add_zero] at F₀
    have Ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
      rw [Fb.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide),
        Ff₁.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact retFrame) (by decide),
        F₀.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact retWs) (by decide)]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact outRet r hr
      · rw [CrtRt.frameR, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨p, hp, rfl⟩
        · exact belowRet
        · have := fR_fit I p hp
          exact retWs.sub_right (Offset.sub_base _ (by omega))
    refine ⟨by rw [freed_mem, freed_gpr _ _ (by decide)]; exact Pt, ⟨?_, ?_, S.nowrap, ?_⟩, Svt, ?_, Ret⟩
    · rw [freed_gpr _ _ (by decide), ediT]; exact S.edi
    · rw [freed_wr, Kt.2.2, wrf]; exact (K.2.2 ▸ S.wr)
    · rw [freed_esp, espt, BitVec.sub_add_cancel, ← sp]; exact S.stk
    · rw [freed_esp, espt, BitVec.sub_add_cancel]
  · obtain ⟨P₂, S₂, Sv₂, esp₂, ret₂⟩ := R₂
    refine WP.mono (Crt.entryRestore_ok S₂ hz Sv₂) fun u Rs => ?_
    refine ⟨by rw [Rs.mem, Rs.other .eax (by decide)]; exact P₂, ?_, by rw [Rs.mem]; exact ret₂⟩
    intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Rs.gpr (.ebx, 32) (by decide)
    · exact Rs.gpr (.esi, 40) (by decide)
    · exact Rs.gpr (.edi, 44) (by decide)
    · exact Rs.gpr (.ebp, 36) (by decide)
    · exact (Rs.other _ (by decide)).trans esp₂


theorem wrap_ok (A : WrapABI a n s) {body : Prog isa} (hsp : NoSp (.seq (.block (fill a)) body))
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {Out : List Region} (outRet : ∀ r ∈ Out, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    (outWs : ∀ r ∈ Out, Region.Disjoint ⟨wsBase a s, wsSize a s⟩ r) {P : Mem → BitVec 32 → Prop}
    (hb : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem →
      WP isa body f fun t => P t.mem (t.gpr .eax) ∧
        Frame (Out ++ CrtRt.frameR (wsBase a s) (f.gpr .esp) (fR (pLenOf a s))) f.mem t.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t) :
    WP isa (wrap a body) s fun u => P u.mem (u.gpr .eax) ∧ abiPreserved s u :=
  wrap_syms_ok A hsp hx outRet outWs fun f I e F _ => hb f I e F

end

end VG.Proof.Ffdh.X86
