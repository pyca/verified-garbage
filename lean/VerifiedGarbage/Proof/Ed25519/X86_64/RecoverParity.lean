module

public import VerifiedGarbage.Impl.Ed25519.X86_64.RecoverSign
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86_64.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.X25519.X86_64.Invert

/-! ### `Ed25519.X86_64.PointEncode`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86_64.PointAffine`, which this module and modules that import it used -/

section

/-! Normalization calls X25519's verified inversion, `vg_gf25519_r64_invert`: the proofs
are of the code with it inlined. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr E F DivstepInv)

variable {fld : Arith} [EdArith fld]

theorem invertWide_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa VG.Impl.X25519.X86_64.invertFn s fun t =>
      (∀ r, r ∉ Proof.X25519.X86_64.clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Proof.X25519.X86_64.Outside base 512 256 s.mem t.mem ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega_using [this]⟩
  obtain ⟨tr, t, he, hg, hr, hw, hm, hv⟩ :=
    Proof.X25519.X86_64.invertFn_pow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hg, rfl, rfl, hm, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := by
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (pointAffine fld).inline s fun t => RbxKeep base s t ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  simp only [Code.inline, VG.Impl.X25519.X86_64.invertCall]
  refine WP.seq (WP.mono (invertWide_ok hs) fun t ⟨hg, hr, hw, hm, hv⟩ => ?_)
  have ht : Scratch t base := ⟨(hg _ (by decide) (by decide)).trans hs.rdi, hw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCodeWide_ok ht affineOps) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hg r hr hb), ku.rd.trans hr,
    ku.wr.trans hw, (hm.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv]
    have he : env t.mem base 0 = env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hm.fe (Or.inl (by decide)) (by decide)]
    rw [he]
  · rw [vu, (affine_eval _).2, hv]
    have he : env t.mem base 1 = env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hm.fe (Or.inl (by decide)) (by decide)]
    rw [he]

end VG.Proof.Ed25519.X86_64

end

end

/-! Canonical point encoding in four machine words. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Keeps val4 fe)

variable {fld : Arith} [EdArith fld]

theorem freezeWide_ok {s : State} {base : Addr} (hs : Scratch s base) (a : Slot) :
    WP isa (.block (VG.Impl.X25519.X86_64.freeze (offset a))) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = (env s.mem base a).val ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx] s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega_using [this]⟩
  obtain ⟨tr, t, he, hv, hk⟩ := Proof.X25519.X86_64.freeze_ok hn (a := offset a) (by simp only [offset]; omega_using [])
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem sign_word (w : BitVec 64) :
    (w &&& (1 : BitVec 32).signExtend 64).rotateRight 1 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega_using [])]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega_using []
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2) * 2 ^ 63) ∧
      Keeps [.rbx] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega_using []
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execShift, show 1 ≤ 1 ∧ 1 ≤ 63 from by decide, and_self, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hv]; exact sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = y)
    (hs : s.gpr .rbx = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.alu .add .r11 (.reg .rbx)]) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.r11] s t := by
  have hb : (s.gpr .r11).toNat < 2 ^ 63 := by simp only [val4] at hv; omega_using [hy, hv]
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega_using []
  have ha : (s.gpr .r11 + s.gpr .rbx).toNat = (s.gpr .r11).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega_using [hb])]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [val4, ha] at hv ⊢; omega_using [hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem pointEncode_ok [X25519.X86_64.DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (pointEncode fld).inline s fun t => RbxKeep base s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  simp only [Code.inline]
  refine WP.seq (WP.mono (pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeWide_ok (ka.scratch hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : RbxKeep base a b := RbxKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : RbxKeep base b c := RbxKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok (kce.scratch (kbe.scratch (ka.scratch hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : RbxKeep base c d := RbxKeep.of_keeps kd (by decide)
  have dx : d.gpr .rbx = BitVec.ofNat 64
      (((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.1 .rbx (by decide), cx, bx, ax]
  rw [kc.2.1, kb.2.1, ay] at dy
  refine WP.mono (encodeSign_ok d _ _ (by
    exact Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (RbxKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.X86_64

end

end

/-! Merged from `Proof.Ed25519.X86_64.FieldCheck`. -/

@[expose] public section

section
/-! Compare field elements through canonical representatives. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem wordsZero_flag (a b c d : BitVec 64) :
    (((a ||| b) ||| c) ||| d == 0#64) = decide (val4 a b c d = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq, val4]
  constructor
  · rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl
  · intro h
    have ha : a.toNat = 0 := by omega_using [h]
    have hb : b.toNat = 0 := by omega_using [h]
    have hc : c.toNat = 0 := by omega_using [h]
    have hd : d.toNat = 0 := by omega_using [h]
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq ha, BitVec.eq_of_toNat_eq hb⟩,
      BitVec.eq_of_toNat_eq hc⟩, BitVec.eq_of_toNat_eq hd⟩

theorem wordsZero_ok (s : State) :
    WP isa (.block wordsZero) s fun t =>
      t.zf = some (decide (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = 0)) ∧
      Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [wordsZero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨wordsZero_flag _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem fieldZero_ok {s : State} {base : Addr} (hs : Scratch s base) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t =>
      t.zf = some (decide (env s.mem base a = 0)) ∧ Keep base s t ∧ t.mem = s.mem := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs a) fun u ⟨uv, ku⟩ => ?_
  refine WP.mono (wordsZero_ok u) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, (Keep.of_keeps ku (by decide)).trans (Keep.of_keeps kt (by decide)), kt.2.1.trans ku.2.1⟩
  rw [tz, uv]
  have he : (env s.mem base a).val = 0 ↔ env s.mem base a = 0 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : Addr} (hs : Scratch s base) (a b : Slot) :
    WP isa (.block (fieldEqual fld a b)) s fun t =>
      t.zf = some (decide (env s.mem base a = env s.mem base b)) ∧ Keep base s t ∧
      ∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs [.sub 21 a b]) fun u ⟨ku, vu⟩ => ?_
  refine WP.mono (fieldZero_ok (hs.of_keep ku) 21) fun t ⟨tz, kt, tm⟩ => ?_
  refine ⟨?_, ku.trans kt, ?_⟩
  · rw [tz, vu]
    change some (decide (env s.mem base a - env s.mem base b = 0)) = _
    have e : env s.mem base a - env s.mem base b = 0 ↔ env s.mem base a = env s.mem base b :=
      ⟨fun h => by grind, fun h => by grind⟩
    simp only [e]
  · intro i hi
    rw [tm, vu]
    change Function.update (env s.mem base) 21 (env s.mem base a - env s.mem base b) i = _
    exact Function.update_of_ne hi _ _

end VG.Proof.Ed25519.X86_64
end

/-! The public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps)

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& (1 : BitVec 32).signExtend 64) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega_using [])]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega_using []
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .rsi = signWord b) :
    WP isa (.block recoverParity) s fun t =>
      t.zf = some (((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 == 1) == b)) ∧
      Keeps [.rax] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega_using []
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self, hs, parity_flag, hv]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov32 .rax (.imm (if b then 1 else 0))]) s fun t =>
      t.gpr .rax = signWord b ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases b <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem testSign_ok {s : State} (b : Bool) (hs : s.gpr .rsi = signWord b) :
    WP isa (.block [.alu .test .rsi (.reg .rsi)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

end VG.Proof.Ed25519.X86_64
