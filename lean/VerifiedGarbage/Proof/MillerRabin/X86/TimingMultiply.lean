module

public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `MillerRabin.X86.TimingCall`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingCallPre`, which this module and modules that import it used -/

section

/-! # Prepared Montgomery calls have public arguments and public limb count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure MulReady (g : Geometry) (capacity b : Nat) (p : BitVec 32) (s : State) : Prop where
  context : Context g s
  modulus : ∃ c, Modulus g c s.mem ∧ val32 s.mem g.W (g.array b) g.words < c
  args : MulArguments g capacity b s
  low : 80 ≤ (s.gpr .esp).toNat
  far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)
  sp : s.gpr .esp = p

theorem MulReady.callPre {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s : State} (R : MulReady g capacity b p s) (length : g.L = 8 * capacity)
    (right : Proof.Rsa.Mont.Operand b) :
    CallPre (Proof.Rsa.Mont.mulContract abi 56) mulArgs [below p 20] [⟨g.W, g.L⟩] s := by
  obtain ⟨c, M, lt⟩ := R.modulus
  have rd : [below p 20] = [⟨argAddr (pushed mulArgs s).callEntry 0, 20⟩] := by
    rw [callEntry_argAddr0, R.sp]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [rd]
    exact mulEntry_pre v R.context length M R.args right lt R.low R.far
  · rw [← R.sp]
    apply Covers.of_mem
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ R.context.ws.wr)
  · apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ R.context.ws.wr

theorem MulReady.width {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s : State} (S : MulReady g capacity b p s) : Proof.Rsa.Mont.wOf (mulEntry g s).mem g.W = g.w := by
  obtain ⟨c, M, _⟩ := S.modulus
  have far := S.far.sub_right (below_sub (by decide : 24 ≤ 80) S.low)
  have frame := mulEntry_frame (by have := S.low; omega_using [this]) S.context.ws.nowrap far
  exact (M.keep v frame (by simp) (by simp)).width


theorem MulReady.publicInputs {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s t : State} (S : MulReady g capacity b p s) (T : MulReady g capacity b p t) :
    (Proof.Rsa.Mont.mulContract abi 56).pub (mulEntry g s) (mulEntry g t) := by
  have sa := fun {i} (hi : i < 5) => mulEntry_arg S.args (by have := S.low; omega_using [this]) hi
  have ta := fun {i} (hi : i < 5) => mulEntry_arg T.args (by have := T.low; omega_using [this]) hi
  have bound : g.W.toNat < 2 ^ 32 := by
    have := S.context.ws.nowrap
    have := v.headerFit
    omega_arith
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  have sp : (mulEntry g s).gpr .esp = (mulEntry g t).gpr .esp := by
    change (pushed mulArgs s).callEntry.gpr .esp = (pushed mulArgs t).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', S.sp, T.sp]
  have width : [Proof.Rsa.Mont.wOf (mulEntry g s).mem g.W] = [Proof.Rsa.Mont.wOf (mulEntry g t).mem g.W] := by
    rw [S.width v, T.width v]
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 5), sa (by decide : 1 < 5), sa (by decide : 2 < 5),
    sa (by decide : 3 < 5), sa (by decide : 4 < 5), ta (by decide : 0 < 5),
    ta (by decide : 1 < 5), ta (by decide : 2 < 5), ta (by decide : 3 < 5), ta (by decide : 4 < 5), ↓reduceIte, ptr]
  exact ⟨sp, width, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # Actual prepared Montgomery calls expose only their public geometry -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem MulReady.entry_eq {g : Geometry} {capacity b : Nat} {p : BitVec 32}
    {s : State} (S : MulReady g capacity b p s) :
    (pushed mulArgs s).callEntry.withRegions [below p 20] [⟨g.W, g.L⟩] = mulEntry g s := by
  unfold mulEntry
  rw [callEntry_argAddr0, S.sp]
  rfl

theorem mulCall_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => MulReady g capacity b p s ∧ MulReady g capacity b p t)
      (.frame (.push mulArgs) (.call name code) (.pop .eax 5)) (fun _ _ => True) := by
  refine VG.X86.RelCT.callWith verified.1 verified.2.1 [below p 20] [⟨g.W, g.L⟩] ?_
  intro s t ⟨S, T⟩
  refine ⟨S.callPre v length right, T.callPre v length right, S.sp.trans T.sp.symm, ?_⟩
  rw [S.entry_eq, T.entry_eq]
  exact S.publicInputs v T

theorem pair_of_keeps {g : Geometry} {s t u z : State} (H : Pair g [.edi] s t)
    (Cu : Context g u) (Cz : Context g z) {rs : List Reg}
    (Ku : Keeps rs s u) (Kz : Keeps rs t z) (sp : .esp ∉ rs) (base : .edi ∉ rs) :
    Pair g [.edi] u z := by
  refine ⟨Cu, Cz, agree_regs ?_⟩
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [Ku.1 .esp sp, Kz.1 .esp sp]
    exact H.2.2.rf.1 .esp (by decide)
  · rw [Ku.1 .edi base, Kz.1 .edi base]
    exact round_regs H.2.2 (by decide)

end VG.Proof.MillerRabin.X86

end

end

/-! # A prepared product retains the round's public base across the call -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.MillerRabin.X86

structure MulInput (g : Geometry) (capacity b : Nat) (p : BitVec 32) (s : State) : Prop where
  context : Context g s
  modulus : ∃ c, Modulus g c s.mem ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array b) g.words < c
  caller : Caller g capacity p s

theorem mulSetup_raw (b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block [.mov .eax (.imm 0), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
    (.block []) rfl rfl rfl rfl

theorem MulInput.setup {g : Geometry} {capacity b : Nat} {p : BitVec 32} {s : State}
    (I : MulInput g capacity b p s) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
      s (MulReady g capacity b p) := by
  refine WP.mono (mulSetup_ok I.context capacity b I.caller.readLen) fun t ⟨A, mem, K⟩ => ?_
  obtain ⟨c, M, _, lt⟩ := I.modulus
  refine ⟨I.context.keepMem K (by decide) mem, ⟨c, ?_, ?_⟩, A, ?_, ?_, ?_⟩
  · rw [mem]; exact M
  · rw [mem]; exact lt
  · rw [K.1 .esp (by decide), I.caller.sp]; exact I.caller.low
  · rw [K.1 .esp (by decide), I.caller.sp]; exact I.caller.stackFar
  · exact (K.1 .esp (by decide)).trans I.caller.sp

theorem mulY_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity b p s ∧ MulInput g capacity b p t)
      (mulY name code b) (fun _ _ => True) := by
  unfold mulY
  refine RelCT.seq (Q := fun _ _ => True) ?_ (mulCall_trace (p := p) verified v length right)
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, _⟩ := mulSetup_raw b _ _ _ _ _ _ H.2.2 E G
  exact ⟨trace, wp_result S.setup E, wp_result T.setup G⟩

theorem mulY_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity b p s ∧ MulInput g capacity b p t)
      (mulY name code b) (Pair g [.edi]) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  have trace := (mulY_trace verified v length right _ _ _ _ _ _ ⟨H, S, T⟩ E G).1
  have post (a : State) (I : MulInput g capacity b p a) :
      WP isa (mulY name code b) a fun t => Context g t ∧ Keeps [.eax, .ecx, .edx] a t := by
    obtain ⟨c, M, odd, lt⟩ := I.modulus
    refine WP.mono (mulY_ok verified noSp stack v I.context length M right odd lt I.caller.readLen
      (by rw [I.caller.sp]; exact I.caller.low) (by rw [I.caller.sp]; exact I.caller.stackFar)) ?_
    intro t R
    exact ⟨R.2.2.2.1, R.2.2.1⟩
  obtain ⟨Cu, Ku⟩ := wp_result (post s S) E
  obtain ⟨Cz, Kz⟩ := wp_result (post t T) G
  exact ⟨trace, pair_of_keeps H Cu Cz Ku Kz (by decide) (by decide)⟩

end VG.Proof.MillerRabin.X86
