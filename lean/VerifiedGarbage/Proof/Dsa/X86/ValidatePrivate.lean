module

public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.PublicKey
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.EntryFrame
import VerifiedGarbage.Proof.Dsa.X86.HeaderFrame
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words32

/-! # Functional correctness of the i686 DSA private-key validator

The domain checker's cdecl entry and width dispatch, whose packed buffer is
now a private key (`3 p_len + 2 q_len` bytes) with the nonce field pointing
at x, around the signer's checks of the domain and the key. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

/-- What `validatePrivateKeyContract` gives the code. -/
structure PrivateValidatingABI (s : State) : Prop where
  stackLow : 108 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  keyScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  keyBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 2).toNat (arg s 3).toNat
  keyLength : (arg s 1).toNat = 3 * (arg s 2).toNat + 2 * (arg s 3).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 2).toNat ≤ (arg s 5).toNat

theorem privateValidatingABI_of {s : State} (h : (Spec.Dsa.validatePrivateKeyContract abi 108).pre s) :
    PrivateValidatingABI s := by
  sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem PrivateValidatingABI.used {s : State} (A : PrivateValidatingABI s) :
    usedBytes ≤ (arg s 5).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega

theorem PrivateValidatingABI.stackArgument {s : State} (A : PrivateValidatingABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem PrivateValidatingABI.stack {s : State} (A : PrivateValidatingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  · exact A.belowScratch

theorem PrivateValidatingABI.room {s : State} (A : PrivateValidatingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  · exact A.belowScratch

/-- A caller's buffer, through another field holding the same pointer. -/
theorem CallerBuffer.retarget {s : State} {base : Addr} {size len : Nat} {p p' : Pointer}
    (B : CallerBuffer s base size p len) (h : pointerValue base s p' = pointerValue base s p) :
    CallerBuffer s base size p' len :=
  ⟨B.room, h ▸ B.fits, h ▸ B.read, h ▸ B.apart, h ▸ B.stack⟩

theorem nonceAtX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block PrevalidatedSign.nonceAtX) s fun t =>
      pointerValue base t (.input .nonce) = pointerValue base s (.input .x) ∧
      Keeps [.eax] s t ∧ Outside base (Layout.field .nonce) 4 s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds .nonce
  have X := VG.Proof.Dsa.X86.Layout.field_bounds .x
  unfold PrevalidatedSign.nonceAtX
  refine wp_movS (readSrc_sc hs (by omega)) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write (by omega)) fun t ut => WP.block_nil ⟨?_, ?_, ?_⟩
  · change t.mem.readW (off base (Layout.field .nonce)) 32 = _
    rw [ut.mem, Mem.readW_writeW_self32, U.gpr]; rfl
  · exact U.keeps.trans (ut.keeps [.eax])
  · rw [ut.mem, U.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

/-- The checker's installation, with the nonce field pointing at x. -/
structure PrivateInstalled (s t : State) : Prop where
  installed : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t
  nonce : pointerValue (argumentPointer s 4) t (.input .nonce) = pointerValue (argumentPointer s 4) t (.input .x)

theorem PrivateInstalled.compare {s t u : State} (I : PrivateInstalled s t)
    (K : Keeps [.eax] t u) (O : u.mem = t.mem) : PrivateInstalled s u :=
  ⟨I.installed.compare K O, by simpa only [pointerValue, O] using I.nonce⟩

theorem privateValidatingEntry_ok {s : State} (A : PrivateValidatingABI s) :
    WP isa (.block PrevalidatedSign.validateEntry) s (PrivateInstalled s) := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  unfold PrevalidatedSign.validateEntry Generate.checkEntry
  refine WP.block_append (WP.mono (installArguments_ok Generate.checkArguments (scratchArg := 4)
    (keyArg := 0) (pLenArg := 2) (qLenArg := 3)
    (A.stackArgument (by decide : 4 < 6)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide)
    (by decide)) fun t1 ⟨Sc, Sv, Args, Q, G, Y, X, K, O⟩ => ?_)
  · intro a ha
    apply A.stackArgument
    simp only [Generate.checkArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · refine WP.mono (nonceAtX_ok Sc (by change 8256 ≤ _; omega)) fun t ⟨N, K2, O2⟩ => ?_
    have B := VG.Proof.Dsa.X86.Layout.field_bounds .nonce
    have Oh : Outside (argumentPointer s 4) 8192 64 t1.mem t.mem :=
      O2.mono B.1 (by have : Layout.saved = 8256 := rfl; omega)
    refine ⟨⟨Sc.of_keeps K2 (by decide), saved_header Oh Sv, fun a ha => ?_,
      (field_keep O2 (by decide)).trans Q, (field_keep O2 (by decide)).trans G,
      (field_keep O2 (by decide)).trans Y, (field_keep O2 (by decide)).trans X,
      K.trans (K2.mono (by decide)),
      O.trans (O2.mono (Nat.zero_le _) (by have : Layout.saved = 8256 := rfl; omega))⟩, ?_⟩
    · have hn : a.2 ≠ .nonce := by
        simp only [Generate.checkArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> decide
      exact (field_keep O2 hn).trans (Args a ha)
    · exact N.trans (field_keep O2 (by decide)).symm

theorem validatePrivateKeyBytes_eq {pLen qLen p q g y x : Nat} {key : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (keyLen : key.length = 3 * pLen + 2 * qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩) :
    Spec.Dsa.validatePrivateKeyBytes pLen qLen key =
      decide (shapeValid p q ∧ publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) := by
  unfold Spec.Dsa.validatePrivateKeyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, keyValue]
  by_cases hs : shapeValid p q
  · have e := privateChecks_spec (g := g) (y := y) (x := x) hs
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, hs, true_and, ← e, and_assoc]
  · have hp : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ := fun P => hs (parametersValid_shape P)
    simp only [hp, hs, decide_false, Bool.false_and, false_and]

theorem privateValidatingSized_spec {base : Addr} {size pLen qLen p q g y x : Nat}
    {s : State} {key : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (X : CallerBuffer s base size (.input .x) qLen)
    (N : pointerValue base s (.input .nonce) = pointerValue base s (.input .x))
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (hx : operandValue s base (.input .x) qLen = x)
    (keyLen : key.length = 3 * pLen + 2 * qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩) :
    WP isa (Generate.checkSizedWith PrevalidatedSign.validateCompute pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePrivateKeyBytes pLen qLen key then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  have value := validatePrivateKeyBytes_eq widths keyLen keyValue
  have K0 := X.retarget N
  have hk : operandValue s base (.input .nonce) qLen = x := by
    simp only [operandValue, N]; exact hx
  unfold Generate.checkSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    unfold PrevalidatedSign.validateCompute
    have Gt := G.keep_shape O K (by decide) (by decide)
    have Yt := Y.keep_shape O K (by decide) (by decide)
    have Xt := X.keep_shape O K (by decide) (by decide)
    have Kt := K0.keep_shape O K (by decide) (by decide)
    have hgt := (G.value_keep_shape O K (by decide) (by decide) bound).trans hg
    have hyt := (Y.value_keep_shape O K (by decide) (by decide) bound).trans hy
    have hxt := (X.value_keep_shape O K (by decide) (by decide) bound).trans hx
    have hkt := (K0.value_keep_shape O K (by decide) (by decide) bound).trans hk
    refine WP.seq (WP.seq (WP.mono (publicKey_ok Mt Gt Yt hgt hyt) fun u ⟨Mu, Fu, _, E⟩ =>
      WP.mono (privateKey_ok Mu (E.buffer Gt (by decide)) (E.buffer Yt (by decide))
        (E.buffer Xt (by decide)) (E.buffer Kt (by decide))
        ((E.value Gt (by decide) Mt.extent).trans hgt) ((E.value Yt (by decide) Mt.extent).trans hyt)
        ((E.value Xt (by decide) Mt.extent).trans hxt) ((E.value Kt (by decide) Mt.extent).trans hkt))
        fun v ⟨Mv, Fv, _, Ev'⟩ => ?_))
    have Ev := E.trans Ev'
    have mask : flagW base (Layout.field .mask) v =
        mask32 (shapeValid p q ∧ publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < x ∧ x < q) ∧
          g ^ x % p = y) := by
      rw [Fv, Fu, F]
      simp only [mask32_and, and_assoc]
    refine WP.mono (result_ok Mv.scr Mv.saved _ mask) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, ((K.mono (by decide)).trans Ev.keeps).trans (Kf.mono (by decide)), ?_, ?_⟩
    · rw [V, value]
      by_cases h : shapeValid p q ∧ publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y
      · simp only [h]; rfl
      · have h' : ¬ (shapeValid p q ∧ publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < x ∧ x < q) ∧
            g ^ x % p = y) := fun H => h ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.2⟩
        simp only [h, h', decide_false, ite_false]; rfl
    · rw [Of]
      intro a ha hstack
      exact (execution_outside Ev a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega)))
    · intro regs saved
      rw [Of]
      exact Ev.saved (shapeFrame_saved O saved)
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (verifyFailure_ok t) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · rw [V, value]
      simp only [valid, false_and, decide_false]
      rfl
    · rw [Of]
      intro a ha _
      exact (shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega))
    · intro regs saved
      rw [Of]
      exact shapeFrame_saved O saved

theorem privateValidatingInstalled_spec {s t : State} (A : PrivateValidatingABI s) (I : PrivateInstalled s t) :
    WP isa (Generate.checkSizedWith PrevalidatedSign.validateCompute (arg s 2).toNat (arg s 3).toNat) t
      fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePrivateKeyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, Bytes⟩ := I.installed.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.installed.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, Value⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr Yptr Xptr
  exact privateValidatingSized_spec I.installed.scr A.used A.lengths P Q G Y X I.nonce rfl rfl rfl rfl rfl
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength) Value

theorem privateValidatingOperation_spec {s : State} (A : PrivateValidatingABI s) :
    WP isa PrevalidatedSign.validate s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePrivateKeyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  unfold PrevalidatedSign.validate Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (privateValidatingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok _ _ I.installed.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.installed.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.installed.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (privateValidatingInstalled_spec A J) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega)
      (by rw [J.installed.keeps.1 .esp (by decide)]; exact hstack)).trans
        (J.installed.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.installed.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.installed.scr.of_keeps K (by decide)) sz
    (Saved s.gpr J.installed.saved)) fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.installed.keeps.2.1]
  · rw [R.wr, K.2.2, J.installed.keeps.2.2]

end VG.Proof.Dsa.X86
