import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyContext
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.RootPair

/-!
# Ed25519 verification on x86-64: both square roots' powers first

`decodePowers` loads the y-coordinates of R and of A, computes the input `u v⁷` of each one's
square root's power, and both powers at once (`rootPower2_ok`): A's into slot 15, where
decoding A takes it, and R's into byte 7680 of the scratch, which decoding A keeps and
`powerRestore` moves back into slot 15 before R is decoded.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside clob F fe fe_st4 st4_outside)

variable {fld : Arith} [EdArith fld]

theorem rootInput3_eval (e : Env) :
    evalOps (rootInputOps 3) e 3 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 :=
  congrArg (rootU (e 1) * ·) (pow_seven _)

theorem rootInput2_eval (e : Env) :
    evalOps (rootInputOps 2) e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 ∧
    evalOps (rootInputOps 2) e 3 = e 3 :=
  ⟨congrArg (rootU (e 1) * ·) (pow_seven _), rfl⟩

private theorem loadY_clob : ∀ r ∈ [Reg.r8, .r9, .r10, .r11, .rax], r ∈ clob := by decide

/-- The y-coordinate at `p` into slot 1, and the power's input of it into slot `o`. -/
theorem decodeInput_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) (o : Slot) :
    WP isa (.block (decodeInput fld o)) s fun t => Keep base s t ∧
      env t.mem base = evalOps (rootInputOps o)
        (Function.update (env s.mem base) 1 (decodedY (Spec.Ed25519.bytesAt s.mem p 32))) := by
  rw [decodeInput, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadY_ok s p hp hr) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  have has : Scratch a base := hs.of_keeps ka (by decide)
  refine WP.mono (storeWordsWide_ok has 1) fun b ⟨bm, bg, brd, bwr⟩ => ?_
  have bo : Outside base (offset 1) 32 a.mem b.mem := by
    rw [bm]; exact st4_outside _ _ (by decide) _ _ _ _
  have be : env b.mem base =
      Function.update (env s.mem base) 1 (decodedY (Spec.Ed25519.bytesAt s.mem p 32)) := by
    rw [env_update 1 bo, ka.2.1]
    refine congrArg (Function.update (env s.mem base) 1) ?_
    rw [F, bm, fe_st4 _ _ (by decide), av]
    rfl
  have kab : Keep base s b :=
    ⟨fun r hr => (bg r).trans (ka.1 r fun hm => hr (loadY_clob r hm)), brd.trans ka.2.2.1,
      bwr.trans ka.2.2.2, by rw [← ka.2.1]; exact bo.mono (by decide) (by decide)⟩
  refine WP.mono (fieldCodeWide_ok (hs.of_keep kab) (rootInputOps o)) fun t ⟨kt, vt⟩ => ?_
  exact ⟨kab.trans kt, by rw [vt, be]⟩

theorem movRaxRdi_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi)]) s fun t => t.gpr .rax = s.gpr .rdi ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem rax_base {s : State} {base : Addr} (hs : Scratch s base) (h : s.gpr .rax = s.gpr .rdi) :
    s.gpr .rax = off base 0 := by
  rw [h, hs.rdi]
  exact (BitVec.add_zero base).symm

/-- Slot 19 to byte 7680. -/
theorem powerSave_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block powerSave) s fun t => PowersKeep base 7680 32 s t ∧
      env t.mem base = env s.mem base ∧ F t.mem base 7680 = env s.mem base 19 := by
  rw [powerSave, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movRaxRdi_ok s) fun a ⟨ap, ka⟩ => ?_
  have has : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsFieldWide_ok has 19) fun b ⟨bv, kb⟩ => ?_
  have hbs : Scratch b base := has.of_keeps kb (by decide)
  have bp : b.gpr .rax = off base 0 :=
    rax_base hbs ((kb.1 _ (by decide)).trans (ap.trans (ka.1 _ (by decide)).symm) |>.trans
      (kb.1 _ (by decide)).symm)
  refine WP.mono (tableWords_ok hbs bp 7680 (by decide)) fun t ⟨tm, tg, trd, twr⟩ => ?_
  rw [Nat.zero_add] at tm
  have hto : Outside base 7680 32 b.mem t.mem := by
    rw [tm]; exact st4_outside _ _ (by decide) _ _ _ _
  have sm : b.mem = s.mem := kb.2.1.trans ka.2.1
  refine ⟨⟨fun r _ _ hr => (congrFun tg r).trans ((kb.1 r fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)).trans
      (ka.1 r fun hm => hr (by rw [List.mem_singleton.mp hm]; decide))),
    trd.trans (kb.2.2.1.trans ka.2.2.1), twr.trans (kb.2.2.2.trans ka.2.2.2),
    TableFrame.table (sm ▸ hto)⟩, by rw [table_env hto (by decide), sm], ?_⟩
  change F t.mem base 7680 = F s.mem base (offset 19)
  rw [F, F, tm, fe_st4 _ _ (by decide), bv, ka.2.1]

/-- Byte 7680 back to slot 15. -/
theorem powerRestore_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block powerRestore) s fun t => Keep base s t ∧
      env t.mem base = Function.update (env s.mem base) 15 (F s.mem base 7680) := by
  rw [powerRestore, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movRaxRdi_ok s) fun a ⟨ap, ka⟩ => ?_
  have has : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok has (rax_base has ((ap.trans (ka.1 _ (by decide)).symm))) 7680
    (by decide)) fun b ⟨bv, kb⟩ => ?_
  refine WP.mono (storeWordsWide_ok (has.of_keeps kb (by decide)) 15) fun t ⟨tm, tg, trd, twr⟩ => ?_
  have hto : Outside base (offset 15) 32 b.mem t.mem := by
    rw [tm]; exact st4_outside _ _ (by decide) _ _ _ _
  have sm : b.mem = s.mem := kb.2.1.trans ka.2.1
  refine ⟨⟨fun r hr => (tg r).trans ((kb.1 r fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)).trans
      (ka.1 r fun hm => hr (by rw [List.mem_singleton.mp hm]; decide))),
    trd.trans (kb.2.2.1.trans ka.2.2.1), twr.trans (kb.2.2.2.trans ka.2.2.2),
    sm ▸ hto.mono (by decide) (by decide)⟩, ?_⟩
  rw [env_update 15 hto, sm]
  refine congrArg (Function.update (env s.mem base) 15) ?_
  rw [F, F, tm, fe_st4 _ _ (by decide), bv, Nat.zero_add, ka.2.1]

/-- Both powers: A's into slot 15 and R's into byte 7680. -/
theorem decodePowers_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (decodePowers fld) s fun t => VerifyKeep base s t ∧
      env t.mem base 15 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem pk 32)) ∧
      F t.mem base 7680 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem sig 32)) := by
  rw [decodePowers]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  refine WP.seq (WP.mono (decodeInput_ok (fld := fld) ha.scratch (ap.trans h.sigHeader) ha.rRead 3)
    fun b ⟨kb, vb⟩ => ?_)
  have kbp : VerifyKeep base a b := PowersKeep.of_keep kb
  have hb := ha.of_keep kbp
  refine WP.seq (WP.mono (loadPointer_ok hb.scratch .rdx 7936 (by decide)) fun c ⟨cp, kc⟩ => ?_)
  have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
  have hc := hb.of_keep kcp
  refine WP.seq (WP.mono (decodeInput_ok (fld := fld) hc.scratch (cp.trans hb.pkHeader) hc.pkRead 2)
    fun d ⟨kd, vd⟩ => ?_)
  have kdp : VerifyKeep base c d := PowersKeep.of_keep kd
  have hd := hc.of_keep kdp
  refine WP.seq (WP.mono (rootPower2_ok hd.scratch) fun e ⟨ke, e15, e19⟩ => ?_)
  have kep : VerifyKeep base d e := PowersKeep.of_rbx ke
  refine WP.mono (powerSave_ok (kep.scratch hd.scratch)) fun t ⟨kt, tv, tf⟩ => ?_
  have ktp : VerifyKeep base e t := kt.mono (by decide) (by decide)
  have bsig : Spec.Ed25519.bytesAt a.mem sig 32 = Spec.Ed25519.bytesAt s.mem sig 32 :=
    verifyKeep_bytes kap h.rFar
  have bpk : Spec.Ed25519.bytesAt c.mem pk 32 = Spec.Ed25519.bytesAt s.mem pk 32 :=
    verifyKeep_bytes ((kap.trans kbp).trans kcp) h.pkFar
  have d2 : env d.mem base 2 = rootU (decodedY (Spec.Ed25519.bytesAt s.mem pk 32)) *
      Spec.X25519.pow (rootV (decodedY (Spec.Ed25519.bytesAt s.mem pk 32))) 7 := by
    rw [vd, (rootInput2_eval _).1, Function.update_self, bpk]
  have d3 : env d.mem base 3 = rootU (decodedY (Spec.Ed25519.bytesAt s.mem sig 32)) *
      Spec.X25519.pow (rootV (decodedY (Spec.Ed25519.bytesAt s.mem sig 32))) 7 := by
    rw [vd, (rootInput2_eval _).2, Function.update_of_ne (by decide), kc.2.1, vb, rootInput3_eval,
      Function.update_self, bsig]
  refine ⟨(((((kap.trans kbp).trans kcp).trans kdp).trans kep).trans ktp), ?_, ?_⟩
  · rw [tv, e15, d2]; rfl
  · rw [tf, e19, d3]; rfl

/-! ## Constant time -/

private theorem seq_pub {P Q : State → Prop} {c c' : Prog isa}
    (hct : RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s Q)
    (hn : RelCT isa (fun s t => Q s ∧ Q t) c' (fun _ _ => True)) :
    RelCT isa (fun s t => P s ∧ P t) (.seq c c') (fun _ _ => True) := by
  have hp := VG.RelCT.wp hct (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) hn

private theorem rdi_rdx_agree {base p : Addr} {s t : State} (hs : s.gpr .rdi = base)
    (ht : t.gpr .rdi = base) (ps : s.gpr .rdx = p) (pt : t.gpr .rdx = p) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rdx]) s t := Taint.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.trans ht.symm
  · exact ps.trans pt.symm)

/-- `decodePowers`' trace, between states with the same context (`hc`), which their keeping
(`hk`) preserves. -/
theorem decodePowers_ct (base pk sig challenge : Addr) (P : State → Prop)
    (hc : ∀ s, P s → VerifyContext s base pk sig challenge)
    (hk : ∀ s t, P s → VerifyKeep base s t → P t) :
    RelCT isa (fun s t => P s ∧ P t) (decodePowers fld) (fun _ _ => True) := by
  have rdiCT {Q : State → Prop} (hq : ∀ s, Q s → P s) {c : Prog isa}
      (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
        (VG.X86_64.taint.check (Taint.ofRegs [.rdi]) c hc).isSome = true) :
      RelCT isa (fun s t => Q s ∧ Q t) c (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree (hc _ (hq _ h.1)).scratch.rdi
      (hc _ (hq _ h.2)).scratch.rdi) h
  have loadWP (d : Nat) (p : Addr) (hd : d + 8 ≤ 8192)
      (hp : ∀ s, P s → s.mem.readW (off base d) 64 = p) (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc d))]) s fun t => P t ∧ t.gpr .rdx = p := by
    refine WP.mono (loadPointer_ok (hc s h).scratch .rdx d hd) fun t ⟨tp, kt⟩ => ?_
    exact ⟨hk s t h (PowersKeep.of_keeps kt (by decide)), tp.trans (hp s h)⟩
  have inputCT {o : Slot} {p : Addr} (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      (VG.X86_64.taint.check (Taint.ofRegs [.rdi, .rdx]) (.block (decodeInput fld o)) hc).isSome = true) :
      RelCT isa (fun s t => (P s ∧ s.gpr .rdx = p) ∧ (P t ∧ t.gpr .rdx = p))
        (.block (decodeInput fld o)) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi, .rdx]) (fun _ _ h => rdi_rdx_agree (hc _ h.1.1).scratch.rdi
      (hc _ h.2.1).scratch.rdi h.1.2 h.2.2) h
  have inputWP (o : Slot) {p : Addr} (hr : ∀ s, P s → ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8)
      (s : State) (h : P s ∧ s.gpr .rdx = p) : WP isa (.block (decodeInput fld o)) s P :=
    WP.mono (decodeInput_ok (hc s h.1).scratch h.2 (hr s h.1) o) fun t ⟨kt, _⟩ =>
      hk s t h.1 (PowersKeep.of_keep kt)
  rw [decodePowers]
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (loadWP 7944 sig (by decide) fun s h => (hc s h).sigHeader) ?_
  refine seq_pub (inputCT (by fld_taint_decide)) (inputWP 3 fun s h => (hc s h).rRead) ?_
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (loadWP 7936 pk (by decide) fun s h => (hc s h).pkHeader) ?_
  refine seq_pub (inputCT (by fld_taint_decide)) (inputWP 2 fun s h => (hc s h).pkRead) ?_
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (fun s h => WP.mono (rootPower2_ok (fld := fld) (hc s h).scratch) fun t ⟨kt, _⟩ =>
      hk s t h (PowersKeep.of_rbx kt)) ?_
  exact rdiCT (fun _ h => h) (by fld_taint_decide)

theorem powerRestore_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) (.block powerRestore)
      (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

end VG.Proof.Ed25519.X86_64
