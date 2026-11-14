module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignAfter
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnInput
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipe
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignReturn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignNoSp
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.PrivContext
import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect

/-! # `vg_rsa_pkcs1_sign_precomputed` on i686: the body and the function

`vg_rsa_pkcs1_sign`'s, with `vg_rsa_private_checked_precomputed` called with
`callArgsP` in place of `vg_rsa_private_checked` (`afterEncP_ok`, `bodyP_ok`,
`signFnP_ok`).
-/

-- separate module: the body's proof builds in parallel with the precondition (`SignP.Contract`).

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Sign
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)
open VG.Proof.Dsa.X86 (allocated)

theorem outgoing_frameP {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) {m : Mem} (F : Frame [⟨byteAddr g.stack, 88⟩] s.mem m) :
    Frame (bodyWrites g) s.mem m := F.sub (by
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [bodyWrites], h.outgoingSubP⟩)

theorem callee_frameP {g : Geometry} {m m' : Mem}
    (F : Frame (privateWrP g ++ [g.calleeRegion]) m m') : Frame (bodyWrites g) m m' := F.sub (by
  intro r hr
  simp only [privateWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)

theorem bodyP_noSp (v : CrtImpl) (w : CrtPImpl) : NoSp (body (privNameP v) (privCodeP v w) callArgsP) := by
  unfold body afterEnc
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.of_all (by decide +kernel))
    (.seq' (.of_all (by decide +kernel)) (.ite' (.of_all (by decide +kernel))
      (.seq' (.of_all (by decide +kernel))
        (.seq' (.call' (VG.Proof.Rsa.X86.PrivChecked.privateCodeP_noSp v w)) (.of_all (by decide +kernel)))))))

theorem allocationP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.frame (.alloc frameBytes) (body (privNameP v) (privCodeP v w) callArgsP) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact bodyP_noSp v w i hi
  · rfl

theorem innerP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.seq (.frame (.alloc frameBytes) (body (privNameP v) (privCodeP v w) callArgsP) (.free frameBytes))
      (.block restore)) :=
  .seq' (allocationP_noSp v w) (.of_all (by decide +kernel))

theorem codeP_noSp (v : CrtImpl) (w : CrtPImpl) : NoSp (code (privNameP v) (privCodeP v w) callArgsP) := by
  intro i hi
  change i ∈ instrs (.frame (.push savedRegisters)
    (.seq (.frame (.alloc frameBytes) (body (privNameP v) (privCodeP v w) callArgsP) (.free frameBytes))
      (.block restore)) (.pop .ebx 4)) at hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · apply innerP_noSp v w i
    simpa only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hi
  · rfl

theorem codeP_sp (v : CrtImpl) (w : CrtPImpl) :
    (code (privNameP v) (privCodeP v w) callArgsP).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.PrivChecked.noSp_allStack (codeP_noSp v w)

theorem afterEncP_ok (v : CrtImpl) (w : CrtPImpl) {g : Geometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}
    {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) (enc : Encoded g bs s) :
    WP isa (afterEnc (privNameP v) (privCodeP v w) callArgsP) s fun t => Context g bs t ∧
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax) (result g bs) ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t := by
  unfold afterEnc
  refine WP.seq (wp_cmpS rfl fun c C Z => WP.block_nil ?_)
  have hc := h.after (by rw [C.mem]; exact Frame.refl _ _) (C.keeps []) (by rw [C.gpr])
  have Hc := H.after (by rw [C.mem]; exact Frame.refl _ _) (C.keeps [])
  have encC : Encoded g bs c := by simpa only [Encoded, C.gpr, C.mem] using enc
  cases encoded : encodeId g.hash (bs 2) g.length with
  | none =>
    have zero : c.gpr .eax = 0 := by simpa only [Encoded, encoded] using encC
    refine WP.ite true (by simp [eval, Z, show s.gpr .eax = 0 by rw [← congrFun C.gpr .eax]; exact zero]) (fun _ => ?_) (by simp)
    refine WP.mono (zeroOut_ok hc) ?_
    rintro t ⟨ht, B, A, F, K⟩
    refine ⟨ht, ?_, ?_, (C.keeps clobbers).trans (K.mono (by decide))⟩
    · rw [result_eq (h.sources 0).length, encoded]
      exact ⟨A, B⟩
    · rw [C.mem] at F
      exact F.sub (by intro r hr; obtain rfl := List.mem_singleton.mp hr
                      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)
  | some em =>
    obtain ⟨one, bytes⟩ : c.gpr .eax = 1 ∧ Spec.Rsa.bytesAt c.mem (byteAddr g.temporary) g.length = em := by
      simpa only [Encoded, encoded] using encC
    refine WP.ite false (by simp [eval, Z, show s.gpr .eax = 1 by rw [← congrFun C.gpr .eax]; exact one]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (callArgsP_ok hc Hc) ?_)
    rintro a ⟨ha, Ha, args, F, K⟩
    have retained : Spec.Rsa.bytesAt a.mem (byteAddr g.temporary) g.length = em := by
      exact (VG.Proof.Rsa.rsa_bytes_frame F (by have := h.valid.maxLength; omega_using [this])
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hc.temporaryArgsP)).trans bytes
    refine WP.seq (WP.mono (private_callP v w ha Ha args retained) ?_)
    rintro b ⟨hb, _, Fb, Kb, out⟩
    refine WP.mono (wipe_ok hb) ?_
    rintro t ⟨ht, _, ax, Ft, Kt⟩
    have output : Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
        Spec.Rsa.bytesAt b.mem (byteAddr g.output) g.length :=
      VG.Proof.Rsa.rsa_bytes_frame Ft (by have := h.valid.maxLength; omega_using [this])
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr
            exact (h.valid.stackOutput.sub_left h.valid.innerSub).symm)
    refine ⟨ht, ?_, ?_, (C.keeps clobbers).trans ((K.mono (by decide)).trans
      ((Kb.mono (by decide)).trans (Kt.mono (by decide))))⟩
    · rw [result_eq (h.sources 0).length, encoded]
      unfold PrivateOut at out
      rw [ax]
      cases r : Spec.Rsa.privateChecked (bs 0) (bs 1) em (bs 3) (bs 4) (bs 5) (bs 6) (bs 7) <;>
        simp only [r, Spec.Rsa.writtenOutcome] at out ⊢ <;> exact ⟨out.1, output.trans out.2⟩
    · have Fc := outgoing_frameP hc F
      rw [C.mem] at Fc
      exact Fc.trans ((callee_frameP Fb).trans (Ft.sub (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)))


theorem bodyP_ok (v : CrtImpl) (w : CrtPImpl) {g : Geometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}
    {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) :
    WP isa (body (privNameP v) (privCodeP v w) callArgsP) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax) (result g bs) ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t := by
  unfold body
  refine WP.seq (WP.mono (encArgs_ok h) ?_)
  rintro a ⟨ha, M, K, dst, len, hash, src, count⟩
  refine WP.seq (WP.mono (encoding_ok ha dst len hash src count) ?_)
  rintro b ⟨hb, Fb, Kb, enc⟩
  have frame : Frame (bodyWrites g) s.mem b.mem := by
    rw [M] at Fb
    apply Fb.sub
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  refine WP.mono (afterEncP_ok v w hb (H.after frame (rs := clobbers) ((K.mono (by decide)).trans (Kb.mono (by decide)))) enc) ?_
  rintro t ⟨_, out, Ft, Kt⟩
  exact ⟨out, frame.trans Ft, (K.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt)⟩


theorem signFnP_ok (v : CrtImpl) (w : CrtPImpl) (s : State) {g : Geometry} {bs : Fin 8 → List Byte}
    {P : BitVec 32} {L : Nat} (h : FnInput g bs s) (H : SPreCtx g bs P L (entered s)) :
    WP isa (code (privNameP v) (privCodeP v w) callArgsP) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (result g bs) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold sigStack at this; omega_using [this]
  have allocation : VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [sigStack, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes] at *
    omega_using [this]
  unfold code
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (innerP_noSp v w) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (bodyP_noSp v w) ?_
  refine WP.mono (bodyP_ok v w (s := entered s) h.context H) ?_
  rintro u ⟨result, frame, rest⟩
  have spU : (VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [VG.Proof.Dsa.X86.freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega_using []
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u).rd ++
        (VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u).wr)
        (addr ((VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega_using [fit, hd] : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega_using [hd])
  refine WP.mono (restore_ok (VG.Proof.Dsa.X86.freed VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes u)
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
      restT.1 .eax (by decide), VG.Proof.Dsa.X86.freed_gpr _ _ (by decide)]
    exact result
end VG.Proof.RsaPkcs1Sig.X86.Sgn
