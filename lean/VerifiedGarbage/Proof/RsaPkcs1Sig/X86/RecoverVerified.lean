module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverBody
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFnInput
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverNoSp
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStages
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverBlocksTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverReleaseTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicPre
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLength
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverObservations
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContractInput
/-! # Complete i686 certificate for precomputed PKCS #1 recovery -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverReturn.lean`, which only this module imported.
section

/-! # The wrapper preserves its caller's return address -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem FnInput.returnWord {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold recoverStack at this; omega
  have savedFrame := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have contains : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Contains ((s.gpr .esp).setWidth 64) (32 / 8) :=
    Region.contains_self _ _
  have savedSeparate : ∀ r ∈ [below (s.gpr .esp) 16],
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    unfold below
    rw [Taint.sub_setWidth low]
    have eq : (s.gpr .esp).setWidth 64 =
        (s.gpr .esp).setWidth 64 - 16 + BitVec.ofNat 64 16 := (BitVec.sub_add_cancel _ _).symm
    have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - 16)
      (by decide : 16 ≤ 16) (by decide : 16 + 4 ≤ 2 ^ 64)
    rw [← eq] at sep
    exact sep
  exact (frame.readW contains h.returnSeparate (by decide)).trans
    (savedFrame.readW contains savedSeparate (by decide))
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverEntryCache.lean`, which only this module imported.
section

/-! # Saving caller registers leaves the precomputed public key unchanged -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem FnInput.enteredCache {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : FnInput g bs s) : Precomputed g bs (entered s) ↔ Precomputed g bs s := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold recoverStack at this; omega
  have F := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have saved : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
    rw [h.savedSp]
    exact h.context.valid.offsetAddr (by decide)
  unfold below at F
  rw [← pushed_esp] at F
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at F
  rw [saved] at F
  have words : Spec.Rsa.wordsAt (entered s).mem (byteAddr (g.sources 3)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength :=
    VG.Proof.Rsa.wordsAt_frame F (by
      have fit := h.context.valid.sourceFits 3
      change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.context.valid.stackSources 3).sub_left h.context.valid.savedSub).symm)
  unfold Precomputed
  rw [words]

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverFn.lean`, which only this module imported.
section

/-! # Callable PKCS #1 signing restores the i686 calling convention -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated freed freed_esp freed_gpr)

theorem recoverFn_ok (v : PublicImpl) (s : State) {g : Geometry} {bs : Fin 4 → List Byte}
    (h : FnInput g bs s) :
    WP isa (code v.name v.code) s fun t => abiPreserved s t ∧
      (Precomputed g bs s → Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax)
        (recovered g bs)) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold recoverStack at this; omega
  have allocation : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [recoverStack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes] at *
    omega
  unfold code
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (inner_noSp v) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (body_noSp v) ?_
  refine WP.mono (body_ok v (s := entered s) h.context) ?_
  rintro u ⟨_, frame, rest, result⟩
  have spU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).rd ++
        (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr)
        (addr ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.Sgn.restore_ok (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u)
    (read 4 (by decide)) (read 8 (by decide)) (read 0 (by decide))) ?_
  rintro t ⟨edi, ebp, esi, memT, restT⟩
  have spT : t.gpr .esp = (pushed savedRegisters s).gpr .esp :=
    (restT.1 .esp (by decide)).trans spU
  have words (i : Nat) (hi : i < 4) := h.savedWord frame i hi
  have mem : t.mem = u.mem := memT
  have savedEdi : t.gpr .edi = s.gpr .edi := by
    rw [edi, spU]; exact words 0 (by decide)
  have savedEbp : t.gpr .ebp = s.gpr .ebp := by
    rw [ebp, spU]; exact words 2 (by decide)
  have savedEsi : t.gpr .esi = s.gpr .esi := by
    rw [esi, spU]; exact words 1 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, spT, mem]
      exact words 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEbp
    · rw [popped_esp, spT, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]; exact h.returnWord frame
  · rw [popped_mem, popped_gpr _ _ _ (by decide) (by decide), mem,
      restT.1 .eax (by decide), freed_gpr _ _ (by decide)]
    intro cache
    exact result (h.enteredCache.mpr cache)
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverTailTiming.lean`, which only this module imported.
section

/-! # The padding check never branches on the precomputed RSA call's status -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem compareReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : CompareReady g bs s) (ht : CompareReady g bs t) : VG.X86.Taint.Agree compareTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem compareThenRelease_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare release)) (fun _ _ => True) := by
  apply pair_seq_ct (cmpArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => cmpArgs_ready h) (fun _ h => cmpArgs_ready h)
  apply pair_seq_ct (compare_relCT.mono (fun _ _ h => compareReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => compare_done h) (fun _ h => compare_done h)
  exact release_relCT

structure Compared (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop extends EncodeDone g bs s where
  flag : s.zf = some (s.gpr .eax == 0)

theorem compare_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : EncodeDone g bs s) :
    WP isa (.block test0) s (Compared g bs) := by
  unfold test0
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨h.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (congrFun F.gpr .esp), ?_⟩, ?_⟩
  · simpa only [Encoded, digestBytes, F.gpr, F.mem] using h.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem tail_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => EncodeDone g bs s ∧ EncodeDone g bs t) tail (fun _ _ => True) := by
  unfold tail
  apply pair_seq_ct (cmp_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.context.sp.trans h.2.context.sp.symm
    · exact encoded_status h.1 h.2)) (fun _ _ _ => trivial))
    (fun _ h => compare_ready h) (fun _ h => compare_ready h)
  apply RelCT.ite
  · intro s t h
    change s.zf = t.zf
    rw [h.1.flag, h.2.flag, encoded_status h.1.toEncodeDone h.2.toEncodeDone]
  · exact zeroOut_relCT.mono
      (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · exact compareThenRelease_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)

theorem encodeReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : EncodeReady g bs s) (ht : EncodeReady g bs t) : VG.X86.Taint.Agree encodeTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.len.trans ht.len.symm
  · exact hs.hash.trans ht.hash.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem afterPub_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) afterPub (fun _ _ => True) := by
  unfold afterPub
  apply pair_seq_ct (save_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
  apply pair_seq_ct (encArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => encArgs_ready h) (fun _ h => encArgs_ready h)
  exact pair_seq_ct (encode_relCT.mono (fun _ _ h => encodeReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => encode_done h) (fun _ h => encode_done h) tail_relCT

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverCallPublic.lean`, which only this module imported.
section

/-! # The nested public operation observes only the shared exponent and key words -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem Context.words_equal {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t) :
    Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength =
      Spec.Rsa.wordsAt t.mem (byteAddr (g.sources 3)) g.preLength := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left ?_
  intro i hi
  have hi := List.mem_range.mp hi
  apply Mem.readW_congr
  intro j hj
  rw [Offset.add_add]
  have bound : 8 * i + j < (bs 3).length := by
    rw [(hs.sources 3).length]
    change 8 * i + j < 8 * g.preLength
    omega
  rw [(hs.sources 3).byte _ bound, (ht.sources 3).byte _ bound]

theorem publicCall_pub {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t)
    (argsS : Arguments g (publicArgument g) 10 s) (argsT : Arguments g (publicArgument g) 10 t) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 96).pub
      (s.callEntry.withRegions (publicRd g) (publicWr g)) (t.callEntry.withRegions (publicRd g) (publicWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 10) => publicArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 10) => publicArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 10), ta (by decide : 0 < 10),
    sa (by decide : 1 < 10), ta (by decide : 1 < 10), sa (by decide : 2 < 10), ta (by decide : 2 < 10),
    sa (by decide : 3 < 10), ta (by decide : 3 < 10), sa (by decide : 4 < 10), ta (by decide : 4 < 10),
    sa (by decide : 5 < 10), ta (by decide : 5 < 10), sa (by decide : 6 < 10), ta (by decide : 6 < 10),
    sa (by decide : 7 < 10), ta (by decide : 7 < 10), sa (by decide : 8 < 10), ta (by decide : 8 < 10),
    sa (by decide : 9 < 10), ta (by decide : 9 < 10), publicArgument, true_and, and_true]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  have pf : g.preLength < 2 ^ 32 := by
    have fit := hs.valid.sourceFits 3
    change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes := (hs.callBytes 1).trans (ht.callBytes 1).symm
  have words := hs.callWords.trans ((hs.words_equal ht).trans ht.callWords.symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytes
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes words
  simp only [byteAddr] at words
  rw [bytes, words]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverBodyTiming.lean`, which only this module imported.
section

/-! # The verifier body relates even calls with inconsistent precomputed moduli -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem publicCall_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => CallReady g bs s ∧ CallReady g bs t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (publicRd g) (publicWr g)
  intro s t h
  exact ⟨publicCall_pre h.1.context h.1.args len, publicCall_pre h.2.context h.2.args len,
    publicCall_pub h.1.context h.2.context h.1.args h.2.args,
    (publicCovers h.1.context).1, (publicCovers h.1.context).2,
    (publicCovers h.2.context).1, (publicCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem callThenCheck_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block pubArgs) (.seq (.call v.name v.code) afterPub)) (fun _ _ => True) := by
  apply pair_seq_ct (pubArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (publicCall_relCT v len) (fun _ h => publicCall_ready v h len)
    (fun _ h => publicCall_ready v h len) afterPub_relCT

structure LengthDone (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  flag : s.zf = some (decide (g.signatureLength = g.length))

theorem length_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s (LengthDone g bs) := by
  refine WP.mono (lengthCheck_ok h) ?_
  rintro t ⟨ht, _, _, flag⟩
  exact ⟨ht, flag⟩

theorem body_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) (body v.name v.code) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (length_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => length_done h) (fun _ h => length_done h)
  apply RelCT.ite
  · intro s t h
    change s.zf.map (! ·) = t.zf.map (! ·)
    rw [h.1.flag, h.2.flag]
  · exact zeroOut_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · intro s t tr ur sf tf h E F
    have len : g.signatureLength = g.length := by
      have flag := h.2
      simpa only [eval, h.1.1.flag, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', decide_eq_true_eq] using flag
    exact callThenCheck_relCT v len s t tr ur sf tf ⟨h.1.1.context, h.1.2.context⟩ E F

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverFnTiming.lean`, which only this module imported.
section

/-! # Stack allocation and saved-register restoration reveal only public addresses -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Proof.Rsa.X86.PrivChecked (sp_agree)
open VG.Proof.Dsa.X86 (allocated)

theorem allocation_state {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) :
    a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem allocation_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    :
    RelCT isa (fun a b => ∃ s t, FnInput g bs s ∧ FnInput g bs t ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes)
        (body v.name v.code) (.free VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, hs, ht, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (allocation_noSp v) ea, Exec.gpr (allocation_noSp v) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (body_relCT v) _ _ _ _ _ _ ⟨hs.context, ht.context⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem recoverFn_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    :
    RelCT isa (fun s t => FnInput g bs s ∧ FnInput g bs t)
      (code v.name v.code) (fun _ _ => True) := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.savedSp.trans h.2.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((allocation_relCT v (g := g) (bs := bs)).mono ?_ (fun _ _ h => h))
      (restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverContract.lean`, which only this module imported.
section

/-! # Precomputed recovery satisfies the shared correctness and timing contract -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

theorem recover_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := recoverFn_ok v s (recover_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro cache hash id
  have out := post cache
  unfold recovered at out
  change Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat = some hash at id
  change Spec.Rsa.written t.mem _ _ _
    ((Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat).bind _) at out
  rw [id, Option.bind_some] at out
  exact out

theorem recover_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := recover_contract_pre s hs
  have it := recover_contract_pre t ht
  rw [← publicGeometry hp, ← publicBytes hp] at it
  exact (recoverFn_relCT v s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 16
    else if a = 131080 then 16
    else if a = 131085 then 32
    else if a = 131088 then 64
    else if a = 131093 then 48
    else if a = 131096 then 1
    else if a = 131105 then 64
    else if a = 131108 then 64
    else if a = 131113 then 160
    else if a = 131116 then 112
    else if a = 131121 then 80
    else if a = 131124 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 64⟩, ⟨20480, 128⟩]
  wr := [⟨4096, 16⟩, ⟨40960, 896⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 16 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 0 := by decide
  have a7 : arg satState 7 = 16384 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 40960 := by decide
  have a10 : arg satState 10 = 112 := by decide
  have a11 : arg satState 11 = 20480 := by decide
  have a12 : arg satState 12 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  have hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId 0 = some h ∧ 16 = h.len := ⟨.md5, rfl, rfl⟩
  sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, recoverStack, hash,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem recover_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack) :=
  ⟨recover_contract_correct v, recover_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
