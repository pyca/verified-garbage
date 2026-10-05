import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointDecode`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.CanonicalY`. -/
section
/-! Canonical decoding checks y before reduction modulo p. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (low63)
open VG.Proof.X25519.X86_64 (val4 Keeps freezeB freezeB_ok mask)

theorem setLow63_ok (s : State) :
    WP isa (.block [.movImm64 .rdx low63]) s fun t => t.gpr .rdx = low63 ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem canonicalMask_ok {s : State} (n : Nat)
    (hm : s.gpr .rcx = mask (decide (Spec.X25519.P ≤ n))) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      t.zf = some (decide (n < Spec.X25519.P)) ∧ Keeps [] s t := by
  have hz : (mask (decide (Spec.X25519.P ≤ n)) == 0#64) = decide (n < Spec.X25519.P) := by
    by_cases h : Spec.X25519.P ≤ n
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ n < Spec.X25519.P)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : n < Spec.X25519.P)]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hm]
  exact ⟨hz, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = n) :
    WP isa (.block canonicalY) s fun t => t.zf = some (decide (n < Spec.X25519.P)) ∧
      Keeps [.rdx, .r12, .r13, .r14, .r15, .rax, .rcx] s t := by
  change WP isa (.block (([.movImm64 .rdx low63] : List Instr) ++ freezeB ++
    [.alu .test .rcx (.reg .rcx)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.setLow63_ok s) fun a ⟨ad, ka⟩ => ?_
  have av : val4 (a.gpr .r8) (a.gpr .r9) (a.gpr .r10) (a.gpr .r11) = n := by
    rw [val4, ka.1 .r8 (by decide), ka.1 .r9 (by decide), ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
    exact hv
  rw [WP.block_append_iff]
  refine WP.mono (freezeB_ok a (by rw [av]; omega) ad) fun b ⟨bc, _, kb⟩ => ?_
  rw [av] at bc
  refine WP.mono (VG.Proof.Ed25519.X86_64.canonicalMask_ok n bc) fun t ⟨tz, kt⟩ => ?_
  exact ⟨tz, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.StoreWords`. -/
section
/-! Save four words in an Ed25519 field slot. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr st4)

theorem storeWordsWide_ok {s : State} {base : Addr} (hs : Scratch s base) (o : Slot) :
    WP isa (.block (Impl.X25519.X86_64.store4 (offset o))) s fun t =>
      t.mem = st4 s.mem base (offset o) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hm, hg, _, _⟩ := Proof.X25519.X86_64.store4_ok hn (o := offset o)
    (by simp only [offset]; omega)
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hm, hg, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
end

/-! Point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside clob F st4_outside fe_st4 val4)

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : VG.Proof.Ed25519.X86_64.DecodeKeep base s t) (k : VG.Proof.Ed25519.X86_64.DecodeKeep base t u) : VG.Proof.Ed25519.X86_64.DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.DecodeKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : VG.Proof.Ed25519.X86_64.DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .rbx ∨ r = .rsi) : VG.Proof.Ed25519.X86_64.DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.2.1]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => VG.Proof.Ed25519.X86_64.DecodeKeep base s t ∧
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      t.zf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P)) := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : VG.Proof.Ed25519.X86_64.DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.1 _ (by decide)).trans hp)
    (by intro d hd; rw [ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.2.1] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.storeWordsWide_ok (kab.scratch hs) 1) fun c ⟨cm, cg, cr, cw⟩ => ?_
  have cmem : Outside base (offset 1) 32 b.mem c.mem := by
    rw [cm]; exact st4_outside _ _ (by decide) _ _ _ _
  have kc : VG.Proof.Ed25519.X86_64.DecodeKeep base b c := ⟨fun r _ _ _ => cg r, cr, cw, cmem.mono (by decide) (by decide)⟩
  have cy : env c.mem base 1 = Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change F c.mem base (offset 1) = _
    rw [F, cm, fe_st4 _ _ (by decide), byval]
  have cv : val4 (c.gpr .r8) (c.gpr .r9) (c.gpr .r10) (c.gpr .r11) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 := by
    rw [val4, cg .r8, cg .r9, cg .r10, cg .r11]; exact byval
  refine WP.mono (VG.Proof.Ed25519.X86_64.canonicalY_ok c _ (Nat.mod_lt _ (by decide)) cv) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz⟩
  · rw [kt.1 .rsi (by decide), cg .rsi, kb.1 .rsi (by decide)]; exact asign
  · rw [kt.2.1]; exact cy

end VG.Proof.Ed25519.X86_64
end

/-! Canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (pointDecode fld) s fun t => VG.Proof.Ed25519.X86_64.DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by exact az)
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx (RbxKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual`. -/
section

/-! Projective comparison implements the specification's pointEqual. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem equalOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (Impl.Ed25519.X86_64.pointEqual fld) s fun t => Keep base s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual (VG.Proof.Ed25519.X86_64.point (env s.mem base) 0 1 2 3)
        (VG.Proof.Ed25519.X86_64.point (env s.mem base) 4 5 6 7)) := by
  rw [Impl.Ed25519.X86_64.pointEqual]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs pointEqualOps) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (hs.of_keep ka) 8 9) fun b ⟨bz, kb, be⟩ => ?_
  have kab := ka.trans kb
  have bx : b.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) := by
    rw [bz, va, (VG.Proof.Ed25519.X86_64.equalOps_eval _).1, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.1]
  apply WP.ite _ bx
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (fieldEqual_ok (hs.of_keep kab) 10 11) fun c ⟨cz, kc, _⟩ => ?_)
    have cy : c.zf = some (decide (env s.mem base 1 * env s.mem base 6 = env s.mem base 5 * env s.mem base 2)) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.2.1, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.2.2]
    apply WP.ite _ cy
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (returnFlag_ok c true) fun t ⟨tr, kt⟩ => ?_
      refine ⟨(kab.trans kc).trans (Keep.of_keeps kt (by decide)), ?_⟩
      simpa only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.X86_64.point, hx, hy, beq_self_eq_true, Bool.and_self] using tr
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.X86_64.point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨kab.trans kt, ?_⟩
    simpa only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.X86_64.point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.WindowByte`. -/
section
/-!
# Verification's bytes: two windows per byte of the scalars

Byte `i` of `k` (and of `S`) gives two digits, high nibble first; after it,
the accumulator represents `[k / 256^i]A - [S / 256^i]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- What a byte of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1832 s.mem t.mem

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed25519.X86_64.ByteKeep base s t) (k : VG.Proof.Ed25519.X86_64.ByteKeep base t u) :
    VG.Proof.Ed25519.X86_64.ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : VG.Proof.Ed25519.X86_64.ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : VG.Proof.Ed25519.X86_64.ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.ByteKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : VG.Proof.Ed25519.X86_64.ByteKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.mem.word (Or.inr (by decide)) (by decide)).trans h.kHeader,
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win k.mem (by decide) (by decide), h.bTab.of_win k.mem (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem ByteKeep.bytesK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : VG.Proof.Ed25519.X86_64.ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : VG.Proof.Ed25519.X86_64.ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

/-! ## Digits from the inputs -/

theorem digitKHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7952 0) ((s.mem (off kp i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitKLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7952 0) ((s.mem (off kp i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7944 32) ((s.mem (off (off sp 32) i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7944 32) ((s.mem (off (off sp 32) i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

/-! ## A byte -/

theorem counterCmp_ok {s : State} {base : Addr} (hs : Scratch s base) (i : Nat) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rbx (.mem (Impl.X25519.X86_64.sc 56)), .alu .cmp .rbx (.imm 32)]) s
      fun t => t.zf = some (decide (i = 32)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 i - (32 : BitVec 32).signExtend 64 == 0) = decide (i = 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hi]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

theorem byteStepA_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa (byteStepA fld dbl) s fun t => t.zf = some (decide (i = 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ VG.Proof.Ed25519.X86_64.ByteKeep base s t := by
  rw [byteStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : VG.Proof.Ed25519.X86_64.ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [VG.Proof.Ed25519.X86_64.scalar_byte (n := 64) hi, ka.bytesK h]
  refine WP.seq (WP.mono (windowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (VG.Proof.Ed25519.X86_64.digitKHigh ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowA_ok hb' bd br (Nat.mod_lt _ (by decide))
    (VG.Proof.Ed25519.X86_64.digitKLow hb' hi (kb.counter.trans av))) fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (VG.Proof.Ed25519.X86_64.counterCmp_ok hc'.scratch i hi (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem byteStepAB_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa (byteStepAB fld dbl) s fun t => t.zf = some (decide (i = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ VG.Proof.Ed25519.X86_64.ByteKeep base s t := by
  rw [byteStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : VG.Proof.Ed25519.X86_64.ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  set S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) with hSdef
  have hbK : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [VG.Proof.Ed25519.X86_64.scalar_byte (n := 64) (by omega), ka.bytesK h]
  have hbS : (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256 := by
    rw [VG.Proof.Ed25519.X86_64.scalar_byte (n := 32) hi, ka.bytesS h]
  have lt16 (b : Byte) : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by have := b.isLt; omega)
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (lt16 _) (lt16 _)
    (VG.Proof.Ed25519.X86_64.digitKHigh ha' (by omega) av) (VG.Proof.Ed25519.X86_64.digitSHigh ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowAB_ok hb' bd br (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (VG.Proof.Ed25519.X86_64.digitKLow hb' (by omega) (kb.counter.trans av)) (VG.Proof.Ed25519.X86_64.digitSLow hb' hi (kb.counter.trans av)))
    fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (batchTest_ok hc'.scratch i (by omega) (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb (by omega), ha'.byteS kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hbK, byte_split S i _ hbS]
    module

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.WindowLoop`. -/
section
/-!
# Verification's loops over the bytes of the scalars

Bytes 63 down to 32 hold digits of `k` alone, bytes 31 down to 0 of both
scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- The loops' invariant, with `c` bytes left. -/
structure WinLoop (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : Rep (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : VG.Proof.Ed25519.X86_64.ByteKeep base s₀ s

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem stepA_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (32 + (j + 1)) t) :
    WP isa (byteStepA fld dbl) t fun u => u.zf = some (decide (j = 0)) ∧ VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (VG.Proof.Ed25519.X86_64.byteStepA_ok (i := 32 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal] at uv; exact uv, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem stepB_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (j + 1) t) :
    WP isa (byteStepAB fld dbl) t fun u => u.zf = some (decide (j = 0)) ∧ VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S j u := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.byteStepAB_ok (i := j) ht.ctx ht.d hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨uz, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal, ht.sVal] at uv; exact uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S 64 s) :
    WP isa (.loop (byteStepA fld dbl) .ne) s (VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (VG.Proof.Ed25519.X86_64.stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

theorem loopB_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S 32 s) :
    WP isa (.loop (byteStepAB fld dbl) .ne) s (VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (VG.Proof.Ed25519.X86_64.stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's equation, from the windows

The windows leave a representative of `[k]A - [S]B`, compared with `-R`: they
are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent
points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (negR fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7552) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  refine WP.mono (fieldCodeWide_ok ((hs.of_keep kae).of_keep kbe) _) fun t ⟨kt, vt⟩ => ?_
  refine ⟨(kae.trans kbe).trans kt, ?_, ?_⟩
  · rw [vt, (VG.Proof.Ed25519.X86_64.negR_eval _).1]
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide),
      b_low 3 (by decide)]
  · rw [vt, (VG.Proof.Ed25519.X86_64.negR_eval _).2, pb, ka.2.1]

/-- Verification's code before the windows, regrouped. -/
def windowPrep (fld : Arith) : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) (aTable fld)) (.block bTable)) (.block (windowInit fld))

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa (VG.Proof.Ed25519.X86_64.windowPrep fld) s fun e => VG.Proof.Ed25519.X86_64.WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [VG.Proof.Ed25519.X86_64.windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  have aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  have ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  have bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch) fun c hc' => ?_
  have kbc : PowersKeep base 56 7752 b c :=
    ⟨fun r _ _ hr => hc'.gpr r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)), hc'.rd, hc'.wr,
      TableFrame.table (hc'.mem.mono (by decide) (by decide))⟩
  have ksc := ksb.trans kbc
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table hc'.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env hc'.mem (by decide)]; exact hb.d
  have cA : TableOf id c.mem base 5376 Aa := fun j hj =>
    ⟨_, ((TableFrame.table hc'.mem).point (by omega) (Or.inr (by omega)) (by omega)), hb.table j hj⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [hc'.table j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (ksc.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64) fun e ⟨ec, eg, er, ew, em⟩ => ?_
  have kde : VG.Proof.Ed25519.X86_64.ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, em.mono (by decide) (by decide)⟩
  have kce : VG.Proof.Ed25519.X86_64.ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksc.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), cR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact cd
  have ctx : WinCtx base challenge sig Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide)⟩
  have hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt e.mem challenge 64) < 256 ^ 64 := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt e.mem challenge 64)
    rwa [show (Spec.Ed25519.bytesAt e.mem challenge 64).length = 64 by
      simp [Spec.Ed25519.bytesAt]] at h
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩,
    kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa (verifyEquationPoints fld dbl) s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.loopA_ok w0) fun f hf' => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.loopB_ok hf') fun g hg => ?_)
  have ksg := kse.trans (PowersKeep.of_byte hg.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.negR_ok (ksg.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksg.trans (PowersKeep.of_keep ku)
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have gv := hg.value
  simp only [pow_zero, Nat.div_one] at gv
  rw [tv, u0, u4, win_tablePoint hg.keep.mem (by decide) (by decide), eR,
    window_equation hA hR gv.proj hR.neg.proj]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyContext`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.VerifyTables`. -/
section
/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movImm64 .rbx 0]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scratch s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).rdi o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.2.1, ka.2.1]
  · rw [table_env kt.mem hlo, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end

/-! The verification inputs remain readable and outside the workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps)

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : VG.Proof.Ed25519.X86_64.DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scratch s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarBytes : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1
  challengeRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VG.Proof.Ed25519.X86_64.VerifyContext s base pk sig challenge) (k : VG.Proof.Ed25519.X86_64.VerifyKeep base s t) :
    VG.Proof.Ed25519.X86_64.VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarBytes _ ‹_›
  · exact h.challengeRead _ ‹_›

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

theorem testResult_ok {s : State} (b : Bool) (hs : s.gpr .rax = signWord b) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

theorem decodedThen_ok {s : State} {base : Addr} {p : Option Spec.Ed25519.Point}
    {next : Prog isa} {P : State → Prop} (hr : DecodeResult base p s)
    (hn : ∀ t, Keeps [] s t → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, Keeps [] s t → p = some a → point (env t.mem base) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  rw [decodedThen]
  cases hp : p with
  | none =>
    rw [hp] at hr
    refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.testResult_ok false hr) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite false (by simp only [eval, tz, Option.map_some, Bool.not_false, Bool.not_true])
    · intro h; contradiction
    · intro _; exact hn t kt hp
  | some a =>
    rw [hp] at hr
    refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.testResult_ok true hr.1) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite true (by simp only [eval, tz, Option.map_some, Bool.not_true, Bool.not_false])
    · intro _; exact hy t a kt hp (by rw [kt.2.1]; exact hr.2)
    · intro h; contradiction

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PointEqualCT`. -/
section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def EqualCTPre (base : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Scratch s base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
      Keep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs pointEqualOps) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (hs.of_keep ka) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (VG.Proof.Ed25519.X86_64.equalOps_eval _).1, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (VG.Proof.Ed25519.X86_64.equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov32 .rax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  · apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)

theorem equalSecond_ct (base : Addr) (u v : Spec.X25519.Fe) :
    RelCT isa (fun s t => (Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scratch t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual fld 10 11)) (.ite .e (.block [.mov32 .rax (.imm 1)]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scratch t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual fld 10 11)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual fld 10 11)) s fun t => t.zf = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun _ k => ?_
    rw [k.1, h.2.1, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (VG.Proof.Ed25519.X86_64.returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : Addr) (p q : Spec.Ed25519.Point) :
    RelCT isa (fun s t => VG.Proof.Ed25519.X86_64.EqualCTPre base p q s ∧ VG.Proof.Ed25519.X86_64.EqualCTPre base p q t)
      (Impl.Ed25519.X86_64.pointEqual fld) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => VG.Proof.Ed25519.X86_64.EqualCTPre base p q s ∧ VG.Proof.Ed25519.X86_64.EqualCTPre base p q t)
      (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : VG.Proof.Ed25519.X86_64.EqualCTPre base p q s) :
      WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
        Scratch t base ∧ t.zf = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (VG.Proof.Ed25519.X86_64.equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨h.1.of_keep kt, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86_64.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (VG.Proof.Ed25519.X86_64.equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The digits are
read through pointers and a counter in the scratch, the same in both runs by
correctness; everything else is public by the taint analysis. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps)
open VG.Impl.X25519.X86_64 (sc)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : RelCT isa (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  VG.RelCT.seq ((VG.RelCT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- Code the taint analysis proves constant time with `rdi` alone public. -/
theorem rdi_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .rdi = base)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree_rdi {x y : State} (h : x.gpr .rdi = y.gpr .rdi) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-! ## Digits -/

/-- The digit's address: the pointer at byte `ptr` plus `add`, and the counter. -/
def digitPrefix (ptr add : Nat) : List Instr :=
  [.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (sc 56))]

theorem digitPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {ptr add : Nat}
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P C : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P) (hc : s.mem.readW (off base 56) 64 = C) :
    WP isa (.block (VG.Proof.Ed25519.X86_64.digitPrefix ptr add)) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rsi = off P add ∧ t.gpr .rax = C := by
  rw [VG.Proof.Ed25519.X86_64.digitPrefix, show ([.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)),
      .mov .rax (.mem (sc 56))] : List Instr) =
    [.mov .rsi (.mem (sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      [.mov .rax (.mem (sc 56))]) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  have hb := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (loadPointer_ok hb .rax 56 (by decide)) fun c ⟨cp, kc⟩ => ?_
  refine ⟨(hb.of_keeps kc (by decide)).rdi, ?_, ?_⟩
  · rw [kc.1 _ (by decide), bp, ap, hp]
  · rw [cp, kb.2.1, ka.2.1, hc]

/-- A digit's code: its address by correctness, the rest by the taint analysis. -/
theorem digit_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {ptr add : Nat} {P : Addr}
    {rest : List Instr} (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31)
    (hP : ∀ x, WinCtx base kp sp A x → x.mem.readW (off base ptr) 64 = P)
    (hpre : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (VG.Proof.Ed25519.X86_64.digitPrefix ptr add))
      (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
      (.block rest) (fun _ _ => True)) :
    RelCT isa (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (VG.Proof.Ed25519.X86_64.digitPrefix ptr add ++ rest)) (fun _ _ => True) := by
  have w (x : State) (h : WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) :=
    VG.Proof.Ed25519.X86_64.digitPrefix_ok h.1.scratch hptr hadd (hP x h.1) h.2
  refine blockAppend_ct ((VG.RelCT.wp (VG.Proof.Ed25519.X86_64.rdi_ct (fun x h => h.1.scratch.rdi) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.2.1.trans hy.2.1.symm, hx.2.2.trans hy.2.2.symm⟩

theorem agree_rsi_rax {x y : State} (h : x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rsi, .rax]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem high_ct : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rsi, index := some .rax }, .shift .shr .rbx 4,
      .alu .test .rbx (.reg .rbx)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rsi, .rax]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rsi_rax h)
    (by fld_taint_decide)

theorem low_ct : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rsi, index := some .rax }, .alu .and .rbx (.imm 15)])
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rsi, .rax]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rsi_rax h)
    (by fld_taint_decide)

theorem prefixK_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (VG.Proof.Ed25519.X86_64.digitPrefix 7952 0))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

theorem prefixS_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (VG.Proof.Ed25519.X86_64.digitPrefix 7944 32))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  RelCT isa (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitKHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C (digitHigh 7952 0) :=
  VG.Proof.Ed25519.X86_64.digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) VG.Proof.Ed25519.X86_64.prefixK_ct VG.Proof.Ed25519.X86_64.high_ct

theorem digitKLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C (digitLow 7952 0) :=
  VG.Proof.Ed25519.X86_64.digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) VG.Proof.Ed25519.X86_64.prefixK_ct VG.Proof.Ed25519.X86_64.low_ct

theorem digitSHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C (digitHigh 7944 32) :=
  VG.Proof.Ed25519.X86_64.digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) VG.Proof.Ed25519.X86_64.prefixS_ct VG.Proof.Ed25519.X86_64.high_ct

theorem digitSLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C (digitLow 7944 32) :=
  VG.Proof.Ed25519.X86_64.digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) VG.Proof.Ed25519.X86_64.prefixS_ct VG.Proof.Ed25519.X86_64.low_ct

/-! ## Windows -/

theorem DigitSpec.of_keep {base : Addr} {s t : State} {digit : List Instr} {v : Nat}
    (h : DigitSpec base s digit v) (k : WinKeep base s t) : DigitSpec base t digit v :=
  fun u ku => h u (k.trans ku)

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, Rep (point (env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigitA_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd fld)))
    (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem addDigitB_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
      (pointAddCached fld))) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr} {v o : Nat}
    (hdig : VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C digit)
    (hadd : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v x ∧ VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .rdi = base ∧ u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, uz, ku⟩ =>
      ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, uv, uz⟩
  refine VG.RelCT.seq (VG.RelCT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩) ?_
  rw [addDigit]
  refine VG.RelCT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ _ => trivial)
  · simp only [eval, h.2.1.2.2, h.2.2.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.2.1.1.trans h.1.2.2.1.symm, h.1.2.1.2.1.trans h.1.2.2.2.1.symm⟩)
      (fun _ _ h => h)

theorem double4_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (VG.Impl.Ed25519.X86_64.double4 fld) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

instance : EdDouble (VG.Impl.Ed25519.X86_64.double4 fld) :=
  ⟨fun hs ha => WP.mono (double4_ok hs ha) fun _ ⟨r, h, k⟩ => ⟨r, h, WinKeep.of_double k⟩, VG.Proof.Ed25519.X86_64.double4_ct⟩

theorem windowA_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C digit) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v x ∧ VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v y)
      (windowA fld dbl digit) (fun _ _ => True) := by
  have hw (x : State) (h : VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v x) :
      WP isa dbl x (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (EdDouble.ok h.ctx.scratch ha) fun b ⟨br, bh, kb⟩ => ?_
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowA]
  exact VG.Proof.Ed25519.X86_64.seq_same (VG.Proof.Ed25519.X86_64.rdi_ct (fun x h => h.ctx.scratch.rdi) (EdDouble.ct (dbl := dbl))) hw (VG.Proof.Ed25519.X86_64.digitAdd_ct hdig VG.Proof.Ed25519.X86_64.addDigitA_ct)

/-- After a window of `k` alone, the next digit's start. -/
theorem windowA_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next : List Instr}
    {v w : Nat} {x : State}
    (h : VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowA fld dbl digit) x (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowA_ok h.1.ctx h.1.d ha h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowAB_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C digitA) (hB : VG.Proof.Ed25519.X86_64.DigitCT base kp sp A C digitB) :
    RelCT isa (fun x y => (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB fld dbl digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact VG.Proof.Ed25519.X86_64.seq_same ((VG.Proof.Ed25519.X86_64.windowA_ct hA).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => VG.Proof.Ed25519.X86_64.windowA_next h) (VG.Proof.Ed25519.X86_64.digitAdd_ct hB VG.Proof.Ed25519.X86_64.addDigitB_ct)

/-- After a window of both scalars, the next digits' start. -/
theorem windowAB_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr}
    {digitA digitB nextA nextB : List Instr} {vA vB wA wB : Nat} {x : State}
    (h : (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (DigitSpec base x nextA wA ∧ wA < 16) ∧ (DigitSpec base x nextB wB ∧ wB < 16)) :
    WP isa (windowAB fld dbl digitA digitB) x fun u =>
      VG.Proof.Ed25519.X86_64.WinPre base kp sp A C nextA wA u ∧ DigitSpec base u nextB wB ∧ wB < 16 := by
  obtain ⟨a, ha⟩ := h.1.1.value
  refine WP.mono (windowAB_ok h.1.1.ctx h.1.1.d ha h.1.1.bound h.1.2.2 h.1.1.digit h.1.2.1)
    fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨⟨h.1.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.1.counter, h.2.1.1.of_keep kb,
    h.2.1.2⟩, h.2.2.1.of_keep kb, h.2.2.2⟩

/-! ## Bytes -/

theorem batchBegin_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchBegin)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

theorem batchTest_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchTest)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

theorem counterCmp_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block [.mov .rbx (.mem (sc 56)), .alu .cmp .rbx (.imm 32)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => VG.Proof.Ed25519.X86_64.agree_rdi h) (by fld_taint_decide)

theorem nibble_lt (b : Nat) : b % 256 / 16 < 16 :=
  Nat.div_lt_of_lt_mul (by have := Nat.mod_lt b (show 256 > 0 by decide); omega)

/-- After `batchBegin`: the counter is `i`, and the scalars' bytes are those of `K` and `S`. -/
theorem byteBegin_ok {s₀ x : State} {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64)
    (h : VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base kp sp A a ∧ env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, Rep (point (env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      (a.mem (off kp i)).toNat = K / 256 ^ i % 256 ∧
      (i < 32 → (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256) := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_
  have ka : VG.Proof.Ed25519.X86_64.ByteKeep base x a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  refine ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩,
    av, ?_, fun hi32 => ?_⟩
  · rw [VG.Proof.Ed25519.X86_64.scalar_byte (n := 64) hi, ka.bytesK h.ctx, h.kVal]
  · rw [VG.Proof.Ed25519.X86_64.scalar_byte (n := 32) hi32, ka.bytesS h.ctx, h.sVal]

theorem byteStepA_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    RelCT isa (fun x y => (∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) y)) (byteStepA fld dbl) (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let vH := K / 256 ^ i % 256 / 16
  let vL := K / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a => VG.Proof.Ed25519.X86_64.WinPre base kp sp A C (digitHigh 7952 0) vH a ∧
        DigitSpec base a (digitLow 7952 0) vL ∧ vL < 16 := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (VG.Proof.Ed25519.X86_64.byteBegin_ok hi h) fun a ⟨actx, ad, av, ac, ak, _⟩ => ?_
    refine ⟨⟨actx, ad, av, ac, ?_, VG.Proof.Ed25519.X86_64.nibble_lt _⟩, ?_, Nat.mod_lt _ (by decide)⟩
    · rw [show vH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact VG.Proof.Ed25519.X86_64.digitKHigh actx hi ac
    · rw [show vL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact VG.Proof.Ed25519.X86_64.digitKLow actx hi ac
  have w3 (x : State) (h : VG.Proof.Ed25519.X86_64.WinPre base kp sp A C (digitLow 7952 0) vL x) :
      WP isa (windowA fld dbl (digitLow 7952 0)) x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).rdi
  rw [byteStepA]
  refine VG.Proof.Ed25519.X86_64.seq_same (VG.Proof.Ed25519.X86_64.rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) VG.Proof.Ed25519.X86_64.batchBegin_ct)
    w1 ?_
  refine VG.Proof.Ed25519.X86_64.seq_same ((VG.Proof.Ed25519.X86_64.windowA_ct VG.Proof.Ed25519.X86_64.digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => VG.Proof.Ed25519.X86_64.windowA_next h) ?_
  exact VG.Proof.Ed25519.X86_64.seq_same (VG.Proof.Ed25519.X86_64.windowA_ct VG.Proof.Ed25519.X86_64.digitKLow_ct) w3 (VG.Proof.Ed25519.X86_64.rdi_ct (fun _ h => h) VG.Proof.Ed25519.X86_64.counterCmp_ct)

theorem byteStepAB_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 32) :
    RelCT isa (fun x y => (∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) y)) (byteStepAB fld dbl) (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kH := K / 256 ^ i % 256 / 16
  let kL := K / 256 ^ i % 256 % 16
  let sH := S / 256 ^ i % 256 / 16
  let sL := S / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        (VG.Proof.Ed25519.X86_64.WinPre base kp sp A C (digitHigh 7952 0) kH a ∧ DigitSpec base a (digitHigh 7944 32) sH ∧
          sH < 16) ∧ (DigitSpec base a (digitLow 7952 0) kL ∧ kL < 16) ∧
          (DigitSpec base a (digitLow 7944 32) sL ∧ sL < 16) := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (VG.Proof.Ed25519.X86_64.byteBegin_ok (by omega) h) fun a ⟨actx, ad, av, ac, ak, as⟩ => ?_
    have as := as hi
    refine ⟨⟨⟨actx, ad, av, ac, ?_, VG.Proof.Ed25519.X86_64.nibble_lt _⟩, ?_, VG.Proof.Ed25519.X86_64.nibble_lt _⟩, ⟨?_, Nat.mod_lt _ (by decide)⟩,
      ⟨?_, Nat.mod_lt _ (by decide)⟩⟩
    · rw [show kH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact VG.Proof.Ed25519.X86_64.digitKHigh actx (by omega) ac
    · rw [show sH = (a.mem (off (off sp 32) i)).toNat / 16 by rw [as]]; exact VG.Proof.Ed25519.X86_64.digitSHigh actx hi ac
    · rw [show kL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact VG.Proof.Ed25519.X86_64.digitKLow actx (by omega) ac
    · rw [show sL = (a.mem (off (off sp 32) i)).toNat % 16 by rw [as]]; exact VG.Proof.Ed25519.X86_64.digitSLow actx hi ac
  have w3 (x : State) (h : VG.Proof.Ed25519.X86_64.WinPre base kp sp A C (digitLow 7952 0) kL x ∧
      DigitSpec base x (digitLow 7944 32) sL ∧ sL < 16) :
      WP isa (windowAB fld dbl (digitLow 7952 0) (digitLow 7944 32)) x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).rdi
  rw [byteStepAB]
  refine VG.Proof.Ed25519.X86_64.seq_same (VG.Proof.Ed25519.X86_64.rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) VG.Proof.Ed25519.X86_64.batchBegin_ct)
    w1 ?_
  refine VG.Proof.Ed25519.X86_64.seq_same ((VG.Proof.Ed25519.X86_64.windowAB_ct VG.Proof.Ed25519.X86_64.digitKHigh_ct VG.Proof.Ed25519.X86_64.digitSHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)) (fun x h => VG.Proof.Ed25519.X86_64.windowAB_next h) ?_
  exact VG.Proof.Ed25519.X86_64.seq_same (VG.Proof.Ed25519.X86_64.windowAB_ct VG.Proof.Ed25519.X86_64.digitKLow_ct VG.Proof.Ed25519.X86_64.digitSLow_ct) w3 (VG.Proof.Ed25519.X86_64.rdi_ct (fun _ h => h) VG.Proof.Ed25519.X86_64.batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` bytes left. -/
def LoopRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ VG.Proof.Ed25519.X86_64.WinLoop s₀ base kp sp A K S c x

theorem loopA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 64 x ∧ VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 64 y)
      (.loop (byteStepA fld dbl) .ne)
      (fun x y => VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 32 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S (32 + n) x ∧
    VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S (32 + n) y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S (32 + (j + 1)) x) :
        WP isa (byteStepA fld dbl) x fun u => u.zf = some (decide (j = 0)) ∧
          VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S (32 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (VG.Proof.Ed25519.X86_64.stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (VG.RelCT.wp ((VG.Proof.Ed25519.X86_64.byteStepA_ct (i := 32 + j) (by omega)).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

theorem loopB_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 32 y)
      (.loop (byteStepAB fld dbl) .ne)
      (fun x y => VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 0 x ∧ VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S 0 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S n x ∧
    VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S n y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S (j + 1) x) :
        WP isa (byteStepAB fld dbl) x fun u => u.zf = some (decide (j = 0)) ∧ VG.Proof.Ed25519.X86_64.LoopRun R₀ base kp sp A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (VG.Proof.Ed25519.X86_64.stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (VG.RelCT.wp ((VG.Proof.Ed25519.X86_64.byteStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scratch s base ∧ Rep (point (env s.mem base) 0 1 2 3) P ∧ Rep (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    RelCT isa (fun s t => VG.Proof.Ed25519.X86_64.EqRepPre base P Q s ∧ VG.Proof.Ed25519.X86_64.EqRepPre base P Q t)
      (Impl.Ed25519.X86_64.pointEqual fld) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => VG.Proof.Ed25519.X86_64.EqRepPre base P Q s ∧ VG.Proof.Ed25519.X86_64.EqRepPre base P Q t)
      (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : VG.Proof.Ed25519.X86_64.EqRepPre base P Q s) :
      WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
        Scratch t base ∧ t.zf = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (VG.Proof.Ed25519.X86_64.equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨h.1.of_keep kt, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (rep_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact rep_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : RelCT isa (fun s t => (Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scratch t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual fld 10 11)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw2 (s : State) (h : Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual fld 10 11)) s fun t => t.zf = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun _ k => by
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := VG.RelCT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.X86_64.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine VG.RelCT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
    · exact fun _ _ h => by simp only [eval, h.2.1, h.2.2]
    · exact (VG.Proof.Ed25519.X86_64.returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTPublic`. -/
section
/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) (kt : VerifyKeep base s t) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs t :=
  ⟨h.context.of_keep kt, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552]) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  all_goals
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r t) (verifyEquationPoints fld dbl) (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r x) :
      WP isa (windowPrep fld) x (LoopRun R₀ base challenge sig Aa K S 64) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarBytes c.scalarFar
      c.challengeRead c.challengeFar (by rw [h.2.1]; exact hA)) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we⟩
  have wn (x : State) (h : LoopRun R₀ base challenge sig Aa K S 0 x) :
      WP isa (.block (negR fld)) x (EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [pow_zero, Nat.div_one] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨hx.ctx.scratch.of_keep ku, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg
  have prepCT : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (windowPrep fld) (fun _ _ => True) := by
    rw [windowPrep]
    exact taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h)
      (by fld_taint_decide)
  have negRCT : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (negR fld)) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  refine seq_same (c₁ := windowPrep fld) (rdi_ct (fun x h => h.1.context.scratch.rdi) prepCT) w ?_
  refine VG.RelCT.seq loopA_ct (VG.RelCT.seq loopB_ct ?_)
  exact seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) negRCT) wn
    (pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTBody`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTAdjust`. -/
section
/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.1 _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    RelCT isa (fun x y => Scratch x base ∧ Scratch y base ∧ x.zf = y.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode fld [.const 5 0, .sub 0 5 0])))
        (.block (recoverSuccess fld))) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun x y => x.gpr .rdi = base ∧ y.gpr .rdi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : RelCT isa (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
      exact fun _ _ _ => Taint.agree_ofRegs (by simp)
    have hw := VG.RelCT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some true) =>
        And.intro (WP.block_nil h.1.1.rdi) (WP.block_nil h.1.2.1.rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct (fld := fld) base).mono
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        ⟨h.1.1.rdi, h.1.2.1.rdi⟩) (fun _ _ h => h)
    have hw := VG.RelCT.wp ht
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        And.intro (WP.mono (fieldCodeWide_ok h.1.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.1.of_keep k.1).rdi)
          (WP.mono (fieldCodeWide_ok h.1.2.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.2.1.of_keep k.1).rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (recoverAdjustSign fld) (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
        Scratch t base ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨h.1.of_keep kt, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86_64
end

/-! The negative-zero check leaks only the public coordinate and sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem testThenSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block [.alu .test .rsi (.reg .rsi)]) (.ite .ne recoverInvalid (recoverAdjustSign fld)))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block [.alu .test .rsi (.reg .rsi)]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block [.alu .test .rsi (.reg .rsi)]) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (!b) := by
    refine WP.mono (testSign_ok b h.2.1) fun t ⟨tz, kt⟩ => ?_
    refine ⟨⟨h.1.of_keeps kt (by simp), (kt.1 _ (by simp)).trans h.2.1, ?_⟩, tz⟩
    rw [kt.2.1]; exact h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2, h.2.2.2]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (recoverSign fld) (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨tz, kt, tm⟩ => ?_
    refine ⟨⟨h.1.of_keep kt, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩, ?_⟩
    · rw [tm]; exact h.2.2
    · rw [tz, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    exact h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def RootCTState (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual fld 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ s.zf = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus))) := by
  have ht : RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual fld 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
      exact fun _ _ h => rdi_agree h.1.1.1.rdi h.2.1.1.rdi
    · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
      exact fun _ _ h => rdi_agree h.1.1.1.rdi h.2.1.1.rdi
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual fld 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨tz, kt, te⟩ => ?_
    refine ⟨⟨⟨h.1.1.of_keep kt, (kt.gpr _ (by decide)).trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCodeWide_ok h.1 [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) fun t ⟨kt, te⟩ => ?_
    refine ⟨h.1.of_keep kt, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual fld 11 12)) (.ite .e
        (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld)) recoverInvalid))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y true) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual fld 11 6)) (.ite .e (recoverSign fld)
        (.seq (.block (fieldEqual fld 11 12)) (.ite .e
          (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld)) recoverInvalid))))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y false) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = signWord b ∧ env s.mem base 1 = y

theorem recoverPoint_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      (recoverPoint fld) (fun _ _ => True) := by
  have ht := (recoverCandidate_ct (fld := fld) base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa (recoverCandidate fld) s (RootCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨⟨kt.scratch h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverPoint]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.PointDecodeCT`. -/
section
/-! Canonical point decoding leaks only its public bytes. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

def DecodeCTPre (base p : Addr) (bs : List Byte) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rdx = p ∧
    (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) ∧ Spec.Ed25519.bytesAt s.mem p 32 = bs

theorem pointDecode_ct (base p : Addr) (bs : List Byte) :
    RelCT isa (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (pointDecode fld) (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : RelCT isa (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (.block pointDecodeLoad) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rdx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base p bs s) :
      WP isa (.block pointDecodeLoad) s fun t => RecoverCTPre base b y t ∧
        t.zf = some (decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P)) := by
    refine WP.mono (pointDecodeLoad_ok h.1 h.2.1 h.2.2.1) fun t ⟨kt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.scratch h.1, ?_, ?_⟩, ?_⟩
    · rw [tb, h.2.2.2]
    · rw [ty, h.2.2.2]
    · rw [tz, h.2.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : Addr} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .rax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.X86_64
end

/-! A decoder's public success flag selects the continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem DecodeResult.of_keeps {base : Addr} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (kt : Keeps [] s t) : DecodeResult base p t := by
  cases p with
  | none => exact (kt.1 _ (by simp)).trans h
  | some p => exact ⟨(kt.1 _ (by simp)).trans h.1, by rw [kt.2.1]; exact h.2⟩

theorem decodedThen_ct (base : Addr) (p : Option Spec.Ed25519.Point) (P : State → Prop) (next : Prog isa)
    (hP : ∀ s t, Keeps [] s t → P s → P t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (.block [.alu .test .rax (.reg .rax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  have hw (s : State) (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
        P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine WP.mono (testResult_ok p.isSome (decodeResult_flag h.2)) fun t ⟨tz, kt⟩ => ?_
    exact ⟨hP s t kt h.1, h.2.of_keeps kt, tz⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      simp only [eval, h.1.2.1.2.2, Option.isSome_none, Bool.not_false,
        Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at he
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! Decoding R and selecting the public equation continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def DecodeRCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧ tablePoint s.mem base 7424 = a

theorem verifyStoreR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (env t.mem base) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7552)) (verifyEquationPoints fld dbl)) (fun _ _ => True) := by
  have ht := (pointTableWrite_ct base 7552 (by decide)).mono
    (fun s t (h : (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (env t.mem base) 0 1 2 3 = r)) => ⟨h.1.1.1.context.scratch.rdi, h.2.1.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7552)) s (PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r) := by
    refine WP.mono (pointTableWrite_ok h.1.1.context.scratch 7552 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    refine ⟨h.1.1.of_keep (kt.mono (by decide) (by decide)), ?_, tv.trans h.2⟩
    exact (kt.mem.point (by decide) (Or.inl (by decide)) (by decide)).trans h.1.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyEquationPoints_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR)

theorem verifyDecodeR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t) (verifyDecodeR fld dbl) (fun _ _ => True) := by
  let P := DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a
  have loadCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.context.scratch.rdi h.2.1.context.scratch.rdi
  have loadWP (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) s fun t =>
        P t ∧ DecodeCTPre base sig rbs t := by
    refine WP.mono (loadPointer_ok h.1.context.scratch .rdx 7944 (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.1.of_keep kp
    exact ⟨⟨hp, by rw [kt.2.1]; exact h.2⟩,
      hp.context.scratch, tp.trans h.1.context.sigHeader, hp.context.rRead, hp.rBytes⟩
  have hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (pointDecode_ct (fld := fld) base sig rbs).mono
    (fun s t (h : (P s ∧ DecodeCTPre base sig rbs s) ∧ (P t ∧ DecodeCTPre base sig rbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ DecodeCTPre base sig rbs s) :
      WP isa (pointDecode fld) s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint rbs) t := by
    have hd := pointDecode_ok (fld := fld) (base := base) (p := sig) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    have kt := ht.1
    exact ⟨⟨h.1.1.of_keep (PowersKeep.of_decode kt),
      (workspace_tablePoint kt.mem (by decide) (by decide)).trans h.1.2⟩, ht.2⟩
  have hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeR]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint rbs) P _
  · intro s t kt h
    exact ⟨h.1.of_keep (PowersKeep.of_keeps kt (by simp)), by rw [kt.2.1]; exact h.2⟩
  · intro r hr
    obtain ⟨Ra, hR⟩ := decodePoint_rep hr
    exact verifyStoreR_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR

end VG.Proof.Ed25519.X86_64
end

/-! Decoding the public key selects the public verification continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem verifyStoreA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => (VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ (VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (env t.mem base) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7424)) (verifyDecodeR fld dbl)) (fun _ _ => True) := by
  have ht := (pointTableWrite_ct base 7424 (by decide)).mono
    (fun s t (h : (VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ (VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (env t.mem base) 0 1 2 3 = a)) => ⟨h.1.1.context.scratch.rdi, h.2.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7424)) s (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a) := by
    refine WP.mono (pointTableWrite_ok h.1.context.scratch 7424 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    exact ⟨h.1.of_keep (kt.mono (by decide) (by decide)), tv.trans h.2⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyDecodeR_ct base pk sig challenge pkbs rbs sbs kbs a hA)

theorem verifyDecodeA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t) (verifyDecodeA fld dbl) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have loadCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.context.scratch.rdi h.2.context.scratch.rdi
  have loadWP (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) s fun t =>
        P t ∧ DecodeCTPre base pk pkbs t := by
    refine WP.mono (loadPointer_ok h.context.scratch .rdx 7936 (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.of_keep kp
    exact ⟨hp, hp.context.scratch, tp.trans h.context.pkHeader, hp.context.pkRead, hp.pkBytes⟩
  have hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (pointDecode_ct (fld := fld) base pk pkbs).mono
    (fun s t (h : (P s ∧ DecodeCTPre base pk pkbs s) ∧ (P t ∧ DecodeCTPre base pk pkbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ DecodeCTPre base pk pkbs s) :
      WP isa (pointDecode fld) s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint pkbs) t := by
    have hd := pointDecode_ok (fld := fld) (base := base) (p := pk) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    exact ⟨h.1.of_keep (PowersKeep.of_decode ht.1), ht.2⟩
  have hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeA]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint pkbs) P _
  · intro s t kt h
    exact h.of_keep (PowersKeep.of_keeps kt (by simp))
  · intro a ha
    obtain ⟨Aa, hA⟩ := decodePoint_rep ha
    exact verifyStoreA_ct base pk sig challenge pkbs rbs sbs kbs a hA

end VG.Proof.Ed25519.X86_64
end

/-! The canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem verifyScalar_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)])
      (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.scratch.rdi h.2.scratch.rdi
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)]) s
        (fun t => t.gpr .rdx = off sig 32) := by
    change WP isa (.block (([.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))] : List Instr) ++
      [.alu .add .rdx (.imm 32)])) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, _⟩ => ?_
    refine WP.mono (add32_ok a .rdx) fun t ⟨tp, _⟩ => ?_
    rw [tp, ap, h.sigHeader]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : RelCT isa (fun s t => s.gpr .rdx = off sig 32 ∧ t.gpr .rdx = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  rw [verifyScalar, List.append_assoc]
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid)) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have ht := (verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ t.cf = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead) fun t ⟨kt, _, tc⟩ => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt), by rw [tc, h.sBytes]⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (verifyDecodeA_ct base pk sig challenge pkbs rbs sbs kbs).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifySetup`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyDecodeR`. -/
section
/-! Reject an invalid R encoding or evaluate the complete equation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

theorem verifyDecodeR_ok {s : State} {base pk sig challenge : Addr}
    {Aa : EPoint dZ} (h : VerifyContext s base pk sig challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa (verifyDecodeR fld dbl) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeR]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (fld := fld) (base := base) (p := sig) ha.scratch (ap.trans h.sigHeader) ha.rRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem sig 32) = decoded at hd
  rw [ka.2.1] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c r kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, equationWithR, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7552 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    have hd := h.of_keep kabcd
    have da : tablePoint d.mem base 7424 = tablePoint s.mem base 7424 := by
      rw [kd.mem.point (by decide) (Or.inl (by decide)) (by decide), kc.2.1,
        workspace_tablePoint kb.mem (by decide) (by decide), ka.2.1]
    obtain ⟨Ra, hRa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyEquationPoints_ok hd.scratch hd.sigHeader hd.challengeHeader
      hd.scalarBytes hd.scalarFar hd.challengeRead hd.challengeFar (by rw [da]; exact hA)
      (by rw [dp, cp]; exact hRa)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, da, verifyKeep_bytes kabcd h.scalarFar, verifyKeep_bytes kabcd h.challengeFar,
      hp, hy, equationWithR]

end VG.Proof.Ed25519.X86_64
end

/-! Reject an invalid public key encoding before computing the equation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

theorem verifyDecodeA_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (verifyDecodeA fld dbl) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeA]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7936 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (fld := fld) (base := base) (p := pk) ha.scratch (ap.trans h.pkHeader) ha.pkRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem pk 32) = decoded at hd
  rw [ka.2.1] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c p kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, decodedEquation, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7424 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    obtain ⟨Aa, hAa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyDecodeR_ok (h.of_keep kabcd) (by rw [dp, cp]; exact hAa))
      fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, verifyKeep_bytes kabcd h.rFar, verifyKeep_bytes kabcd h.scalarFar,
      verifyKeep_bytes kabcd h.challengeFar, hp, hy, decodedEquation]

end VG.Proof.Ed25519.X86_64
end

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .rax = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono (verifyScalar_ok h.scratch h.sigHeader h.scalarRead) fun a ⟨ka, am, ac⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ ac
  · intro ht
    refine WP.mono (verifyDecodeA_ok (h.of_keep kap)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.X86_64
end

/-! Save the ABI registers and retain the three public input pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside ea_at word_writeW_sep word_writeW_self)

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov .rdx (.reg .rcx)]) s fun t =>
      t.gpr .rax = s.gpr .rdx ∧ t.gpr .rdx = s.gpr .rcx ∧ Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .rdi = base ∧ (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .rdi ∧
      t.mem.readW (off base 7944) 64 = s.gpr .rsi ∧
      t.mem.readW (off base 7952) 64 = s.gpr .rax := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_self _ _ _
  · exact RegUpd.gpr_setReg_of_ne _ _ hr
  · exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_setReg, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .rdi)]) s fun t =>
      t.gpr .rdx = s.gpr .rdi ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.X86_64
end

/-! Verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 64⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 64) (bytesAt s.mem (s.gpr .rdx) 64))
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧
    bytesAt s.mem (s.gpr .rdi) 32 = bytesAt t.mem (t.gpr .rdi) 32 ∧
    bytesAt s.mem (s.gpr .rsi) 64 = bytesAt t.mem (t.gpr .rsi) 64 ∧
    bytesAt s.mem (s.gpr .rdx) 64 = bytesAt t.mem (t.gpr .rdx) 64

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
  saved : Saved (s.gpr .rcx) s.gpr t.mem
  frame : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem
  rsp : t.gpr .rsp = s.gpr .rsp

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hret, hn⟩ := hs
  have hws : (⟨s.gpr .rcx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok asc (ka.2.2.2 ▸ hws)) fun b ⟨gb, rb, wb, mb, svb⟩ => ?_
  have bs : b.gpr .rdx = s.gpr .rcx := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.2.2.2]; exact hws))
    fun c ⟨cs, gc, rc, wc, mc, cp, cr, cc⟩ => ?_
  have fm : Frame [⟨s.gpr .rcx, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.2.1] at f
    exact f
  have sv : Saved (s.gpr .rcx) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.1
    simp only [Impl.X25519.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.2.2.1)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.2.2.2)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.1 .rdi (by decide)]
    · rw [cr, gb, ka.1 .rsi (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .rsi) 32) d = off (s.gpr .rsi) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi; exact farScratch hpk hi (by decide)
    · intro i hi; exact farScratch hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact farScratch hsig (by omega) (by decide)
    · intro i hi; exact farScratch hchallenge hi (by decide)
  exact ⟨hc, sv, fm, by rw [gc _ (by decide), gb, ka.1 _ (by decide)]⟩

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa (verifyEquation fld dbl) s fun t => gprPreserved s t ∧ verifyLocal.post s t := by
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  have hret := hs.2.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ke⟩ => ?_
  have er : e.gpr .rdx = s.gpr .rcx := es.trans (kd.scratch hc.scratch).rdi
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.2.2.2, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.2.1]; exact svd)) fun t ⟨tr, gt, mt, _, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.rbx, 0) (by decide)
    · exact tr (.rbp, 8) (by decide)
    · rw [gt _ (by decide), ke.1 _ (by decide), kd.gpr _ (by decide) (by decide) (by decide),
        hc0.rsp]
    · exact tr (.r12, 16) (by decide)
    · exact tr (.r13, 24) (by decide)
    · exact tr (.r14, 32) (by decide)
    · exact tr (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem := by
      rw [mt, ke.2.1]; exact fm.trans (scratchFrame md (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  · change t.gpr .rax = _
    rw [gt _ (by decide), ke.1 _ (by decide), dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCT`. -/
section
/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide)⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyBody_rdi_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid))
      (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) :
      WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid)) s
        (fun t => t.gpr .rdi = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).rdi
  exact (VG.RelCT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub (verifyEquation fld dbl) := by
  have setupCT : RelCT isa (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rcx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  rw [verifyEquation]
  refine VG.RelCT.seq hp ?_
  intro s t ts tt s' t' ⟨_, a, b, hab, ha, hb⟩ es et
  have pa := ha.public hab.1
  have pb := hb.public_right hab.2.1 hab.2.2
  exact VG.RelCT.seq
    (verifyBody_rdi_ct (a.gpr .rcx) (a.gpr .rdi) (a.gpr .rsi) (a.gpr .rdx)
      (bytesAt a.mem (a.gpr .rdi) 32) (bytesAt a.mem (a.gpr .rsi) 32)
      (bytesAt a.mem (off (a.gpr .rsi) 32) 32) (bytesAt a.mem (a.gpr .rdx) 64))
    (verifyFinish_ct (a.gpr .rcx)) _ _ _ _ _ _ ⟨pa, pb⟩ es et

end VG.Proof.Ed25519.X86_64
end

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def verifySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

/-- Every load of MXCSR by the code is between saving it in `r11` and loading
it back (`ctlOk`): checked by evaluating it, for each `fld` and `dbl` it is
registered with. -/
abbrev MxcsrOk (c : Prog isa) : Prop := ctlOk c = true

theorem verify_ok (hmx : MxcsrOk (verifyEquation fld dbl)) (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa (verifyEquation fld dbl) s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verify_correct (fld := fld) (dbl := dbl) hs
  exact ⟨t, s', he, abiPreserved_of_ctl hmx he h.1, h.2⟩

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract X86_64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, verifyLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs]
    change t.gpr .rax = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] [verifySatState] using verifySatState

theorem verify_verified (hmx : MxcsrOk (verifyEquation fld dbl)) :
    Verified X86_64.target (verifyEquation fld dbl) (Spec.Ed25519.verifyEquationContract X86_64.abi) :=
  Verified.of_correct (verify_ok hmx) verify_ct verify_implies

end VG.Proof.Ed25519.X86_64

end
