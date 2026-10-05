import VerifiedGarbage.Impl.X25519.AArch64.Word
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.AArch64.Verified
import VerifiedGarbage.Impl.X25519.AArch64.Small
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Slots`. -/
section

/-! The four-word field backend in X25519's existing 4 KiB workspace. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Scratch (s : State) (base : Addr) := Scr s base false

def swapped (e : Env) (x y : VG.Impl.Ed25519.AArch64.Slot) (sw : Bool) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem swapField_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base)
    (x y : VG.Impl.Ed25519.AArch64.Slot) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.cswap (offset x) (offset y))) s fun t =>
      Keep base s t ∧ env t.mem base = VG.Proof.X25519.AArch64.Word.swapped (env s.mem base) x y sw ∧ t.gpr .x3 = s.gpr .x3 := by
  have hsep : offset x + 32 ≤ offset y ∨ offset y + 32 ≤ offset x := by
    have : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    simp only [offset]; omega
  refine WP.mono (VG.Proof.Ed25519.AArch64.cswap_ok hs
    (slot_rangeWith (large := false) x) (slot_rangeWith (large := false) y) hsep hm)
    fun t ⟨hg, hm3, hr, hw, hp, ⟨m, h₁, h₂, hx⟩, _, hy⟩ => ?_
  refine ⟨⟨hg, hr, hw, hp, (h₁.mono (by simp [offset]) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp [offset]) (by simp only [offset]; omega))⟩, ?_, hm3⟩
  have ex : F m base (offset x) = if sw then env s.mem base y else env s.mem base x := by
    change Proof.X25519.toFe _ = _
    rw [hx]
    cases sw <;> rfl
  have ey : F t.mem base (offset y) = if sw then env s.mem base x else env s.mem base y := by
    change Proof.X25519.toFe _ = _
    rw [hy]
    cases sw <;> rfl
  rw [env_update y h₂, env_update x h₁, ex, ey]
  rfl

/-- The coordinate formulas after the conditional swaps. -/
def core (e : Env) : Spec.X25519.Ladder :=
  let a := e 1 + e 2
  let aa := a * a
  let b := e 1 - e 2
  let bb := b * b
  let ee := aa - bb
  let da := (e 3 - e 4) * a
  let cb := (e 3 + e 4) * b
  ⟨aa * bb, ee * (aa + ee * e 18),
    (da + cb) * (da + cb), e 0 * ((da - cb) * (da - cb)), 0⟩

theorem stepOps_eval (e : Env) :
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 1 = (VG.Proof.X25519.AArch64.Word.core e).x2 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 2 = (VG.Proof.X25519.AArch64.Word.core e).z2 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 3 = (VG.Proof.X25519.AArch64.Word.core e).x3 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 4 = (VG.Proof.X25519.AArch64.Word.core e).z3 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 0 = e 0 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 18 = e 18 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Formula`. -/
section

/-! The shared field operations implement precisely the RFC 7748 ladder formulas. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

def Good (e : Env) (x1 : Fe) (st : Ladder) : Prop :=
  e 0 = x1 ∧ e 1 = st.x2 ∧ e 2 = st.z2 ∧ e 3 = st.x3 ∧ e 4 = st.z3 ∧ e 18 = a24

theorem formula_ok (e : Env) (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat)
    (hg : VG.Proof.X25519.AArch64.Word.Good e x1 st) :
    VG.Proof.X25519.AArch64.Word.Good (evalOps VG.Impl.X25519.AArch64.Word.stepOps
      (VG.Proof.X25519.AArch64.Word.swapped (VG.Proof.X25519.AArch64.Word.swapped e 1 3 ((st.swap ^^^ VG.Proof.X25519.bit k t) == 1)) 2 4
        ((st.swap ^^^ VG.Proof.X25519.bit k t) == 1))) x1 (ladderStep k x1 st t) := by
  obtain ⟨h0, h1, h2, h3, h4, hc⟩ := hg
  obtain ⟨e2, ez2, e3, ez3, e0, ec⟩ := VG.Proof.X25519.AArch64.Word.stepOps_eval
    (VG.Proof.X25519.AArch64.Word.swapped (VG.Proof.X25519.AArch64.Word.swapped e 1 3 ((st.swap ^^^ VG.Proof.X25519.bit k t) == 1)) 2 4 ((st.swap ^^^ VG.Proof.X25519.bit k t) == 1))
  unfold VG.Proof.X25519.AArch64.Word.Good
  rw [e0, e2, ez2, e3, ez3, ec, ladderStep_eq]
  by_cases hswap : st.swap ^^^ VG.Proof.X25519.bit k t = 1 <;>
    simp [VG.Proof.X25519.AArch64.Word.core, VG.Proof.X25519.AArch64.Word.swapped,
      Spec.X25519.cswap, hswap, h0, h1, h2, h3, h4, hc, Fin.mul_comm]

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Memory`. -/
section

/-! Frames for the ladder, including its saved swap bit. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64

structure LoopKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 712 s.mem t.mem

theorem LoopKeep.refl (base : Addr) (s : State) : VG.Proof.X25519.AArch64.Word.LoopKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem LoopKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t)
    (k : VG.Proof.X25519.AArch64.Word.LoopKeep base t u) : VG.Proof.X25519.AArch64.Word.LoopKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem LoopKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t)
    (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) : VG.Proof.X25519.AArch64.Word.Scratch t base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem LoopKeep.of_field {base : Addr} {s t : State} (h : Keep base s t) : VG.Proof.X25519.AArch64.Word.LoopKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem LoopKeep.of_invert {base : Addr} {s t : State} (h : IKeep base s t) : VG.Proof.X25519.AArch64.Word.LoopKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem LoopKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hr : ∀ r ∈ rs, r ∈ clob ∨ r = .x19) : VG.Proof.X25519.AArch64.Word.LoopKeep base s t := by
  refine ⟨fun r hc hn => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hr r hm with hr | hr
    · exact hc hr
    · exact hn hr
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem LoopKeep.bit {base : Addr} {s t : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t)
    {i : Nat} (hi : i < 255) :
    t.mem (off base (VG.Impl.X25519.AArch64.Word.BITS + i)) =
      s.mem (off base (VG.Impl.X25519.AArch64.Word.BITS + i)) := by
  apply h.mem
  rw [ofs_off' base (by simp [VG.Impl.X25519.AArch64.Word.BITS,
    VG.Impl.X25519.AArch64.BITS, VG.Impl.X25519.AArch64.slot,
    VG.Impl.X25519.AArch64.NSLOT]; omega)]
  right
  simp [VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
    VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]
  omega

theorem LoopKeep.saved {base : Addr} {s t : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t)
    {i : Nat} (hi : i < 6) : VG.Proof.Ed25519.AArch64.word t.mem base (8*i) = VG.Proof.Ed25519.AArch64.word s.mem base (8*i) :=
  h.mem.word (by omega) (by omega)

theorem LoopKeep.output {base : Addr} {s t : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t) :
    VG.Proof.Ed25519.AArch64.word t.mem base 48 = VG.Proof.Ed25519.AArch64.word s.mem base 48 := h.mem.word (by decide) (by decide)

theorem env_swap_store (m : Mem) (base : Addr) (v : BitVec 64) :
    env (m.writeW (off base 768) v) base = env m base := by
  funext i
  simp only [env, F]
  rw [(writeW_outside m base v (by decide : 768+8<2^64)).fe
    (by simp only [offset]; omega) (by simp only [offset]; omega)]

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Head`. -/
section

/-! Load a scalar bit and turn the old/new swap XOR into a selection mask. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev bitOffset := VG.Impl.X25519.AArch64.Word.BITS

theorem bitOffset_lt : VG.Proof.X25519.AArch64.Word.bitOffset + 255 < 4096 := by decide

theorem bitAddress (base : Addr) (i : Nat) :
    base + BitVec.ofNat 64 i + BitVec.ofNat 64 VG.Proof.X25519.AArch64.Word.bitOffset = off base (VG.Proof.X25519.AArch64.Word.bitOffset+i) := by
  rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem loadBit_ok {base : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) {i kt : Nat}
    (hi : i < 255) (hkt : kt ≤ 1) (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hb : s.mem (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) = BitVec.ofNat 8 kt) :
    WP isa (.block [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19,
      .ldrb .x2 .x8 VG.Proof.X25519.AArch64.Word.bitOffset]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x2 = BitVec.ofNat 64 kt ∧
      Keeps [.x19,.x8,.x2] s t := by
  have hdec : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 i := by
    rw [hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hpre : WP isa (.block [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x8 = base + BitVec.ofNat 64 i ∧
      Keeps [.x19,.x8] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (d := .x19) (n := .x19) (imm := 1) (by decide),
      exec_add, read_x, RegUpd.gpr_write, BitVec.setWidth_eq, hdec, hs.x0,
      ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  change WP isa (.block (([.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19] : List Instr) ++
    [.ldrb .x2 .x8 VG.Proof.X25519.AArch64.Word.bitOffset])) s _
  rw [WP.block_append_iff]
  refine WP.mono hpre fun t ⟨ht, ha, hk⟩ => ?_
  have hr : InRegions (t.rd ++ t.wr) (t.gpr .x8 + BitVec.ofNat 64 VG.Proof.X25519.AArch64.Word.bitOffset) 1 := by
    rw [ha, VG.Proof.X25519.AArch64.Word.bitAddress]
    exact ⟨⟨base,4096⟩, List.mem_append_right _ (hk.wr ▸ hs.wr),
      Offset.contains_base base (d := VG.Proof.X25519.AArch64.Word.bitOffset+i) (n := 1) (by have := VG.Proof.X25519.AArch64.Word.bitOffset_lt; omega) (by have := VG.Proof.X25519.AArch64.Word.bitOffset_lt; omega)⟩
  apply WP.of_runBlock
  have he := VG.Proof.X25519.AArch64.exec_ldrb (s := t) (t := .x2) (n := .x8)
    (off := VG.Proof.X25519.AArch64.Word.bitOffset) (by decide) hr
  rw [runBlock_cons, he, runStep_some]
  have hv : ((t.mem.read (t.gpr .x8 + BitVec.ofNat 64 VG.Proof.X25519.AArch64.Word.bitOffset) 1).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 kt := by
    rw [ha, VG.Proof.X25519.AArch64.Word.bitAddress, VG.Proof.X25519.AArch64.read1_toNat, hk.mem, hb]
    rcases (by omega : kt=0 ∨ kt=1) with rfl | rfl <;> rfl
  simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (hk.mono (by decide)).trans ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), ht]
  · exact RegUpd.gpr_write_self _ _ _ _ |>.trans hv
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; grind)


theorem storeSwap_ok {base : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) :
    WP isa (.block [VG.Impl.Ed25519.AArch64.st .x2 768]) s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
      VG.Proof.Ed25519.AArch64.word t.mem base 768 = s.gpr .x2 ∧ t.gpr = s.gpr := by
  refine WP.block_cons_iff.mpr ⟨_, store_sc hs (d := 768) (by decide) (by decide) .x2, WP.block_nil ?_⟩
  exact ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl,
    (writeW_outside s.mem base (s.gpr .x2) (by decide : 768+8<2^64)).mono (by decide) (by decide)⟩,
    VG.Proof.X25519.AArch64.Word.env_swap_store _ _ _, Mem.readW_writeW_self64 _ _ _, rfl⟩

theorem swapMask_ok {s : State} {sw kt : Nat} (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 sw) (h2 : s.gpr .x2 = BitVec.ofNat 64 kt) :
    WP isa (.block [.logic .eor .x .x3 .x3 .x2, .movz .x .x10 0 0,
      .sub .x .x3 .x10 .x3]) s fun t =>
      t.gpr .x3 = mask ((sw ^^^ kt) == 1) ∧ Keeps [.x3,.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.X25519.AArch64.exec_eor_x, VG.Proof.X25519.AArch64.exec_movz,
    VG.Proof.X25519.AArch64.exec_sub_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [h3, h2, VG.Proof.X25519.AArch64.ofNat_xor hsw hkt]
    exact VG.Proof.X25519.AArch64.maskB_of (VG.Proof.X25519.AArch64.xor_le hsw hkt)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]


theorem prefix_ok {base : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) {i sw kt : Nat}
    (hi : i < 255) (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hswap : VG.Proof.Ed25519.AArch64.word s.mem base 768 = BitVec.ofNat 64 sw)
    (hb : s.mem (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) = BitVec.ofNat 8 kt) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.stepPrefix) s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x3 = mask ((sw ^^^ kt) == 1) ∧
      VG.Proof.Ed25519.AArch64.word t.mem base 768 = BitVec.ofNat 64 kt := by
  change WP isa (.block (([.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19,
    .ldrb .x2 .x8 VG.Proof.X25519.AArch64.Word.bitOffset] : List Instr) ++
    ([VG.Impl.Ed25519.AArch64.ld .x3 768] ++
    ([VG.Impl.Ed25519.AArch64.st .x2 768] ++
    [.logic .eor .x .x3 .x3 .x2, .movz .x .x10 0 0, .sub .x .x3 .x10 .x3])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.loadBit_ok hs hi hkt hc hb) fun a ⟨ac, ak, ka⟩ => ?_
  have kla : VG.Proof.X25519.AArch64.Word.LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (kla.scratch hs) (d := 768) (by decide) (by decide) .x3)
    fun b ⟨bs, kb⟩ => ?_
  have klb : VG.Proof.X25519.AArch64.Word.LoopKeep base s b := kla.trans (LoopKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.storeSwap_ok (klb.scratch hs)) fun c ⟨klc, ec, sc, gc⟩ => ?_
  have ck : c.gpr .x2 = BitVec.ofNat 64 kt := by rw [gc, kb.gpr _ (by decide), ak]
  have cs : c.gpr .x3 = BitVec.ofNat 64 sw := by rw [gc, bs, ka.mem, hswap]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.swapMask_ok hsw hkt cs ck) fun t ⟨tm, km⟩ => ?_
  refine ⟨(klb.trans klc).trans (LoopKeep.of_keeps km (by decide)), ?_, ?_, tm, ?_⟩
  · rw [km.mem, ec, kb.mem, ka.mem]
  · rw [km.gpr _ (by decide), gc, kb.gpr _ (by decide), ac]
  · rw [km.mem, sc, kb.gpr _ (by decide), ak]

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Small`. -/
section

/-! The single-row constant multiplication shares the checked carry fold. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

theorem moveHigh_ok (s : State) :
    WP isa (.block [VG.Impl.Ed25519.AArch64.mov .x20 .x21, .movz .w .x11 38 0]) s fun t =>
      t.gpr .x20 = s.gpr .x21 ∧ t.gpr .x11 = 38 ∧ Keeps [.x20,.x11] s t := by
  change WP isa (.block (([.addImm .x .x20 .x21 0] : List Instr) ++ [.movz .w .x11 38 0])) s _
  rw [WP.block_append_iff]
  have hm : WP isa (.block [.addImm .x .x20 .x21 0]) s fun t =>
      t.gpr .x20 = s.gpr .x21 ∧ Keeps [.x20] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec_addImm_x (imm := 0) (by decide),
      VG.Proof.Ed25519.AArch64.read_x,BitVec.add_zero,Option.some.injEq,exists_eq_left']
    exact ⟨RegUpd.gpr_write_self _ _ _ _,⟨fun r hr =>
      RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩⟩
  refine WP.mono hm fun a ⟨av,ka⟩ => ?_
  refine WP.mono (movz38_ok a) fun t ⟨tv,kt⟩ => ?_
  exact ⟨(kt.gpr _ (by decide)).trans av,tv,(ka.mono (by decide)).trans (kt.mono (by decide))⟩

theorem mulA24_ok {s : State} {base : Addr} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) (o a : VG.Impl.Ed25519.AArch64.Slot) :
    WP isa (.block (VG.Impl.X25519.AArch64.mulA24 (offset o) (offset a))) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o (env s.mem base a * 121665) := by
  rw [VG.Impl.X25519.AArch64.mulA24]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun b ⟨bz,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b .x3 121665) fun c ⟨cv,kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.loads_ok ((hs.of_keeps kb (by decide)).of_keeps kc (by decide))
    (slot_rangeWith (large := false) a) (by decide)) fun d ⟨d12,d13,d14,d15,kd⟩ => ?_
  have dz : d.gpr .x10 = 0 := by rw [kd.gpr _ (by decide),kc.gpr _ (by decide),bz]
  rw [WP.block_append_iff]
  refine WP.mono (rowFirst_ok d dz) fun e ⟨ev,ke⟩ => ?_
  have ep : val4 (e.gpr .x4) (e.gpr .x5) (e.gpr .x6) (e.gpr .x7) + 2^256*(e.gpr .x21).toNat =
      121665 * fe s.mem base (offset a) := by
    rw [kd.gpr _ (by decide),cv,show (121665 : BitVec 64).toNat = 121665 from rfl,
      d12,d13,d14,d15,kc.mem,kb.mem] at ev
    exact ev
  have eh : (e.gpr .x21).toNat < 2^52 := by
    have hh := val4_lt (VG.Proof.Ed25519.AArch64.word s.mem base (offset a)) (VG.Proof.Ed25519.AArch64.word s.mem base (offset a+8))
      (VG.Proof.Ed25519.AArch64.word s.mem base (offset a+16)) (VG.Proof.Ed25519.AArch64.word s.mem base (offset a+24))
    change fe s.mem base (offset a) < 2^256 at hh
    omega_using [ep,hh]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.moveHigh_ok e) fun f ⟨fh,f38,kf⟩ => ?_
  have fz : f.gpr .x10 = 0 := by rw [kf.gpr _ (by decide),ke.gpr _ (by decide),dz]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok f fz f38 (by rw [fh]; exact eh)) fun g ⟨gv,kg⟩ => ?_
  have kk : Keeps clob s g := (((((kb.mono (by decide)).trans (kc.mono (by decide))).trans
    (kd.mono (by decide))).trans (ke.mono (by decide))).trans (kf.mono (by decide))).trans (kg.mono (by decide))
  refine WP.mono (store4_ok (hs.of_keeps kk (by decide)) (slot_rangeWith (large := false) o)) fun t ht => ?_
  subst t
  have om := st4_outside g.mem base (by simp only [offset]; omega : offset o+32<2^64)
    (g.gpr .x4) (g.gpr .x5) (g.gpr .x6) (g.gpr .x7)
  have ov : Outside base (offset o) 32 s.mem (st4 g.mem base (offset o) (g.gpr .x4) (g.gpr .x5) (g.gpr .x6) (g.gpr .x7)) := by
    rw [← kk.mem]; exact om
  refine ⟨⟨kk.gpr,kk.rd,kk.wr,kk.sp,ov.mono (by simp [offset]) (by simp only [offset]; omega)⟩,?_⟩
  rw [env_update o ov]
  apply congrArg (Function.update (env s.mem base) o)
  change toFe (fe _ _ _) = _
  rw [fe_st4 _ _ (by simp only [offset]; omega),gv,fh,kf.gpr _ (by decide),kf.gpr _ (by decide),
    kf.gpr _ (by decide),kf.gpr _ (by decide)]
  have ee : toFe (121665 * fe s.mem base (offset a)) =
      toFe (val4 (e.gpr .x4) (e.gpr .x5) (e.gpr .x6) (e.gpr .x7) + 38*(e.gpr .x21).toNat) := by
    rw [← ep]
    apply toFe_congr
    exact fold256 _ _
  rw [← ee]
  exact toFe_mul rfl |>.trans (by simp only [show toFe 121665 = (121665 : Fe) from rfl,env,F]; exact Fin.mul_comm _ _)
end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Step`. -/
section

/-! One complete four-word ladder iteration. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem stepFields_ok {base : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base)
    (hc : env s.mem base 18 = 121665) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.stepFields) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps VG.Impl.X25519.AArch64.Word.stepOps (env s.mem base) := by
  rw [VG.Impl.X25519.AArch64.Word.stepFields,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka,ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.mulA24_ok (ka.scr hs) 2 11) fun b ⟨kb,eb⟩ => ?_
  refine WP.mono (fieldCode_ok _ (kb.scr (ka.scr hs))) fun t ⟨kt,et⟩ => ?_
  refine ⟨ka.trans (kb.trans kt),?_⟩
  rw [et,eb,ea]
  have he : evalOp (.mul 2 11 18) (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base)) =
      Function.update (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base)) 2
        (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base) 11 * 121665) := by
    have hp : evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base) 18 =
        env s.mem base 18 := rfl
    simp only [evalOp,hp,hc]
  rw [← he]
  rfl

theorem step_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} {st : Ladder} {i : Nat}
    (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) (hi : i < 255) (hg : VG.Proof.X25519.AArch64.Word.Good (env s.mem base) x1 st)
    (hsw : st.swap ≤ 1) (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hw : VG.Proof.Ed25519.AArch64.word s.mem base 768 = BitVec.ofNat 64 st.swap)
    (hb : s.mem (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k i)) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.step) s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ VG.Proof.X25519.AArch64.Word.Good (env t.mem base) x1 (ladderStep k x1 st i) ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ VG.Proof.Ed25519.AArch64.word t.mem base 768 = BitVec.ofNat 64 (VG.Proof.X25519.bit k i) := by
  simp only [VG.Impl.X25519.AArch64.Word.step, VG.Impl.X25519.AArch64.Word.stepHead,
    VG.Impl.X25519.AArch64.Word.cswap, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.prefix_ok hs hi hsw (bit_le k i) hc hw hb) fun a ⟨ka, ea, ca, ma, wa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.swapField_ok (ka.scratch hs) 1 3 (by decide) ma) fun b ⟨kb, eb, mb⟩ => ?_
  have kab : VG.Proof.X25519.AArch64.Word.LoopKeep base s b := ka.trans (LoopKeep.of_field kb)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.swapField_ok (kab.scratch hs) 2 4 (by decide) (mb.trans ma)) fun c ⟨kc, ec, _⟩ => ?_
  have kac : VG.Proof.X25519.AArch64.Word.LoopKeep base s c := kab.trans (LoopKeep.of_field kc)
  refine WP.mono (VG.Proof.X25519.AArch64.Word.stepFields_ok (kac.scratch hs) (by
    rw [ec,eb,ea]; exact hg.2.2.2.2.2)) fun t ⟨kt, et⟩ => ?_
  refine ⟨kac.trans (LoopKeep.of_field kt), ?_, ?_, ?_⟩
  · rw [et, ec, eb, ea]
    exact VG.Proof.X25519.AArch64.Word.formula_ok _ k x1 st i hg
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), ca]
  · rw [kt.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64),
      kc.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64),
      kb.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64), wa]

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder`. -/
section

/-! The 255 public-count ladder iterations and the final conditional swaps. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem setCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t =>
      t.gpr .x19 = n.setWidth 64 ∧ Keeps [.x19] s t := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr =>
    RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩

def LInv (base : Addr) (s₀ : State) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop :=
  VG.Proof.X25519.AArch64.Word.LoopKeep base s₀ s ∧ VG.Proof.X25519.AArch64.Word.Good (env s.mem base) x1 (ladderAfter k x1 n) ∧
  s.gpr .x19 = BitVec.ofNat 64 n ∧ VG.Proof.Ed25519.AArch64.word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 n).swap

theorem ladder_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base)
    (hg : VG.Proof.X25519.AArch64.Word.Good (env s.mem base) x1 (init x1)) (hw : VG.Proof.Ed25519.AArch64.word s.mem base 768 = 0)
    (hb : ∀ i < 255, s.mem (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k i)) :
    WP isa VG.Impl.X25519.AArch64.Word.ladder s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ VG.Proof.X25519.AArch64.Word.Good (env t.mem base) x1 (ladderAfter k x1 0) ∧
      VG.Proof.Ed25519.AArch64.word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 0).swap := by
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.setCounter_ok s 255) fun a ⟨ac, ka⟩ => ?_)
  have kla : VG.Proof.X25519.AArch64.Word.LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 255 ∧ VG.Proof.X25519.AArch64.Word.LInv base s k x1 n t)
    ?_ 255 a ⟨by decide, by decide, kla, by simpa [ka.mem, ladderAfter_255] using hg, ac,
      by rw [ka.mem, ladderAfter_255]; exact hw⟩
  intro n t ⟨h1, h255, kt, gt, ct, wt⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega⟩
  refine WP.mono (VG.Proof.X25519.AArch64.Word.step_ok (k := k) (kt.scratch hs) (by omega) gt
    (ladderAfter_swap_le _ _ (by omega)) ct wt (by rw [kt.bit (by omega)]; exact hb i (by omega)))
    fun u ⟨ku, gu, cu, wu⟩ => ?_
  have klu : VG.Proof.X25519.AArch64.Word.LoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega)] at gu
  have ws : VG.Proof.Ed25519.AArch64.word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega)]
    exact wu
  have he : isa.eval (.nonzero .x .x19) u = some (decide (i ≠ 0)) := by
    simp only [eval, read_x, cu, counter_nonzero (by omega : i < 2^64)]
  by_cases hi : i=0
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws⟩
  · exact .inr ⟨by rw [he]; simp [hi], i, by omega, by omega, by omega, klu, gu, cu, ws⟩


theorem lastMask_ok {s : State} {sw : Nat} (hsw : sw ≤ 1)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 sw) :
    WP isa (.block [.movz .x .x10 0 0, .sub .x .x3 .x10 .x3]) s fun t =>
      t.gpr .x3 = VG.Proof.Ed25519.Word64.mask (sw == 1) ∧ Keeps [.x3,.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.X25519.AArch64.exec_movz, VG.Proof.X25519.AArch64.exec_sub_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [h3]; exact VG.Proof.X25519.AArch64.maskB_of hsw
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem lastSwap_ok {base : Addr} {s : State} {x1 : Fe} {st : Ladder}
    (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) (hg : VG.Proof.X25519.AArch64.Word.Good (env s.mem base) x1 st) (hsw : st.swap ≤ 1)
    (hw : VG.Proof.Ed25519.AArch64.word s.mem base 768 = BitVec.ofNat 64 st.swap) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.lastSwap) s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ env t.mem base 1 = (Spec.X25519.cswap st.swap st.x2 st.x3).1 ∧
      env t.mem base 2 = (Spec.X25519.cswap st.swap st.z2 st.z3).1 := by
  change WP isa (.block (([VG.Impl.Ed25519.AArch64.ld .x3 768] : List Instr) ++
    ([.movz .x .x10 0 0, .sub .x .x3 .x10 .x3] ++
    (VG.Impl.Ed25519.AArch64.cswap (offset 1) (offset 3) ++
    VG.Impl.Ed25519.AArch64.cswap (offset 2) (offset 4))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := 768) (by decide) (by decide) .x3) fun a ⟨aw, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.lastMask_ok hsw (aw.trans hw)) fun b ⟨bm, kb⟩ => ?_
  have kab : VG.Proof.X25519.AArch64.Word.LoopKeep base s b := (LoopKeep.of_keeps ka (by decide)).trans
    (LoopKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.swapField_ok (kab.scratch hs) 1 3 (by decide) bm) fun c ⟨kc, ec, mc⟩ => ?_
  have kac := kab.trans (LoopKeep.of_field kc)
  refine WP.mono (VG.Proof.X25519.AArch64.Word.swapField_ok (kac.scratch hs) 2 4 (by decide) (mc.trans bm)) fun t ⟨kt, et, _⟩ => ?_
  refine ⟨kac.trans (LoopKeep.of_field kt), ?_, ?_⟩ <;>
    rw [et, ec, kb.mem, ka.mem] <;>
    obtain ⟨h0,h1,h2,h3,h4,h18⟩ := hg <;>
    by_cases hw : st.swap = 1 <;>
    simp [VG.Proof.X25519.AArch64.Word.swapped, Spec.X25519.cswap, hw, h1, h2, h3, h4]

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Input`. -/
section

/-! Decode RFC 7748 inputs into four-word fields. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Kp := VG.Proof.X25519.AArch64.Kp
abbrev Sc := VG.Proof.X25519.AArch64.Sc

theorem outside_frame {base : Addr} {m m' : Mem} {d n : Nat}
    (h : Outside base d n m m') (hn : d+n ≤ 4096) : Frame [⟨base,4096⟩] m m' := by
  intro x hx
  apply h x
  have hh := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hh
  right
  change d+n ≤ (x-base).toNat
  omega

theorem base_ok {base : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Sc base s)
    (hn : base.toNat + 4096 ≤ 2^64) :
    WP isa (.block [VG.Impl.X25519.AArch64.st .x0 48, mov .x1 .x0, mov .x0 .x3]) s fun t =>
      VG.Proof.X25519.AArch64.Word.Scratch t base ∧ t.gpr .x1 = s.gpr .x0 ∧ VG.Proof.Ed25519.AArch64.word t.mem base 48 = s.gpr .x0 ∧
      VG.Proof.X25519.AArch64.Word.Kp [.x0,.x1] s t ∧ Outside base 48 8 s.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_st hs .x0 (off := 48) (by decide), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, mov,
    exec_addImm_x (by decide : 0 < 4096), read_x, BitVec.add_zero, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨hs.x3,hs.wr,hn⟩, trivial, Mem.readW_writeW_self64 _ _ _,
    ⟨fun r hr => by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false],rfl,rfl⟩,
    writeW_outside _ _ _ (by decide)⟩

theorem initGood (e : Env) (x : Fe) (hx : e 0 = x) :
    VG.Proof.X25519.AArch64.Word.Good (evalOps ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) e) x (init x) :=
  ⟨hx, rfl, rfl, hx, rfl, rfl⟩


theorem decode_ok {base p : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base)
    (hp : s.gpr .x2 = p)
    (hr : ∀ d, d+8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block (loadY ++ store4 (offset 0))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = toFe (decodeUCoordinate (bytesAt s.mem p 32)) := by
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok s p hp hr) fun a ⟨av,ka⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps ka (by decide)) (slot_rangeWith (large := false) 0)) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ka.gpr r (fun hh => hr (by simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at *; grind)),
    ka.rd,ka.wr,ka.sp,?_,⟩,?_,⟩
  · rw [ka.mem]
    exact (st4_outside _ _ (by decide : offset 0+32<2^64) _ _ _ _).mono (by decide) (by decide)
  · change toFe (fe _ _ _) = _
    rw [fe_st4 _ _ (by decide), av, VG.Proof.Ed25519.decodeLE_eq,
      decodeUCoordinate_eq (length_bytesAt _ _ _)]
    rfl

theorem init_ok {base : Addr} {s : State} {x : Fe} (hs : VG.Proof.X25519.AArch64.Word.Scratch s base)
    (hx : env s.mem base 0 = x) :
    WP isa (.block (fieldCode ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) ++
      ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr))) s fun t =>
      VG.Proof.X25519.AArch64.Word.LoopKeep base s t ∧ VG.Proof.X25519.AArch64.Word.Good (env t.mem base) x (init x) ∧ VG.Proof.Ed25519.AArch64.word t.mem base 768 = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka,ea⟩ => ?_
  have ga := VG.Proof.X25519.AArch64.Word.initGood (env s.mem base) x hx
  rw [← ea] at ga
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have kb : Keeps [.x2] a (a.write .x .x2 0) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩
  have kab := (LoopKeep.of_field ka).trans (LoopKeep.of_keeps kb (by decide))
  refine WP.mono (VG.Proof.X25519.AArch64.Word.storeSwap_ok (kab.scratch hs)) fun t ⟨kt,et,wt,_⟩ => ?_
  exact ⟨kab.trans kt, by rw [et,RegUpd.mem_write]; exact ga,
    wt.trans (RegUpd.gpr_write_self _ _ _ _)⟩


theorem LoopKeep.kp {base : Addr} {s t : State} (h : VG.Proof.X25519.AArch64.Word.LoopKeep base s t) :
    VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hc => hr (List.mem_append_left _ hc))
    (fun hc => hr (List.mem_append_right _ (by simp [hc]))),h.rd,h.wr⟩

theorem savedBits {base : Addr} {m m' : Mem}
    (hf : Frame [VG.Proof.X25519.AArch64.bitsArea base] m m') {i : Nat} (hi : i < 6) :
    VG.Proof.Ed25519.AArch64.word m' base (8*i) = VG.Proof.Ed25519.AArch64.word m base (8*i) := by
  apply BitVec.eq_of_toNat_eq
  have hh := VG.Proof.X25519.AArch64.save_frame (b := base) (k := i) hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.saveR_disj _ (by decide) (by decide)) hi
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using hh

theorem savedInitial {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, VG.Proof.X25519.AArch64.wd m base (VG.Impl.X25519.AArch64.SAVE+8*i) =
      (g (VG.Impl.X25519.AArch64.saved.getD i .x19)).toNat) {i : Nat} (hi : i < 6) :
    VG.Proof.Ed25519.AArch64.word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19) := by
  apply BitVec.eq_of_toNat_eq
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using h i hi

theorem setup_ok {base sc pt : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Word.Sc base s)
    (hn : base.toNat+4096 ≤ 2^64) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc,32⟩ : Region) ∈ s.rd) (hpr : (⟨pt,32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hdP : (⟨pt,32⟩ : Region).Disjoint ⟨base,4096⟩) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.setup) s fun t =>
      VG.Proof.X25519.AArch64.Word.Scratch t base ∧ VG.Proof.X25519.AArch64.Word.Good (env t.mem base) (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))) ∧
      VG.Proof.Ed25519.AArch64.word t.mem base 768 = 0 ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ i < 255, t.mem (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) = BitVec.ofNat 8 (VG.Proof.X25519.bit (decodeScalar25519 (bytesAt s.mem sc 32)) i)) ∧
      (∀ i < 6, VG.Proof.Ed25519.AArch64.word t.mem base (8*i) = s.gpr (VG.Impl.X25519.AArch64.saved.getD i .x19)) ∧
      VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x0,.x1,.x19] : List Reg)) s t := by
  rw [VG.Impl.X25519.AArch64.Word.setup]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.save_ok hs) fun a ⟨sv,fa,ka⟩ => ?_
  have hsa := hs.of_kp ka (by decide)
  have fsa : ∀ r ∈ [VG.Proof.X25519.AArch64.saveR base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact Region.sub_of_ble rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.bits_ok hsa
    (by rw [ka.gpr _ (by simp),h1])
    (fun i hi => ⟨_,List.mem_append_left _ (ka.rd ▸ hsr),Offset.contains_base sc (by omega) (by omega)⟩)
    (fun i hi r hr => by
      rw [List.mem_singleton.mp hr]
      exact hdS.sub_right (VG.Proof.X25519.AArch64.sub_scR base (d := VG.Impl.X25519.AArch64.BITS) (n := 256) (by decide)) _
        (Offset.contains_base sc (by omega) (by omega)))) fun b ⟨bb,fb,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.base_ok (hsa.of_kp kb (by decide)) hn) fun c ⟨hsc,oc,wc,kc,fc⟩ => ?_
  have fsc := VG.Proof.X25519.AArch64.Word.outside_frame fc (by decide)
  have fsb : ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.sub_scR _ (by decide)
  have bp : bytesAt c.mem pt 32 = bytesAt s.mem pt 32 := by
    rw [VG.Proof.X25519.AArch64.bytesAt_out fsc (by simp only [List.mem_singleton,forall_eq]; exact Region.sub_of_ble rfl) hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fb fsb hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fa fsa hdP]
  change WP isa (.block ((loadY ++ store4 (offset 0)) ++
    (fieldCode [.copy 3 0,.const 1 1,.const 2 0,.const 4 1,.const 18 121665] ++
    ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr)))) c _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.decode_ok hsc (by rw [kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by simp),h2])
    (fun d hd => ⟨_,List.mem_append_left _ (by rw [kc.rd,kb.rd,ka.rd]; exact hpr),
      Offset.contains_base pt (by omega) (by omega)⟩)) fun d ⟨kd,xd⟩ => ?_
  rw [bp] at xd
  refine WP.mono (VG.Proof.X25519.AArch64.Word.init_ok (kd.scr hsc) xd) fun t ⟨kt,gt,wt⟩ => ?_
  have ft : Outside base 48 728 b.mem t.mem :=
    (fc.mono (by decide) (by decide)).trans
      ((kd.mem.mono (by decide) (by decide)).trans (kt.mem.mono (by decide) (by decide)))
  refine ⟨kt.scratch (kd.scr hsc),gt,wt,?_,?_,?_,?_,⟩
  · rw [kt.gpr _ (by decide) (by decide), kd.gpr _ (by decide),oc,
      kb.gpr _ (by decide),ka.gpr _ (by simp)]
  · intro i hi
    rw [ft (off base (VG.Proof.X25519.AArch64.Word.bitOffset+i)) (by
      right; rw [ofs_off' base (by have := VG.Proof.X25519.AArch64.Word.bitOffset_lt; omega)]; have := VG.Proof.X25519.AArch64.Word.bitOffset_lt; change 776 ≤ VG.Proof.X25519.AArch64.Word.bitOffset+i; simp only [VG.Proof.X25519.AArch64.Word.bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS, VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]; omega), bb i (by omega)]
    exact VG.Proof.X25519.AArch64.clampB_eq (fun j hj => VG.Proof.X25519.AArch64.byte_out fa fsa hdS hj) hi
  · intro i hi
    rw [ft.word (Or.inl (by omega)) (by omega), VG.Proof.X25519.AArch64.Word.savedBits fb hi]
    exact VG.Proof.X25519.AArch64.Word.savedInitial sv hi
  · exact (((ka.trans kb).trans kc).trans
      ((LoopKeep.of_field kd).trans kt).kp).sub (by decide)

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Lit`. -/
section

namespace VG
materialize_code Impl.X25519.AArch64.Word.x25519
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Output`. -/
section

/-! Canonical field encoding and restoration of the caller's registers. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

theorem restore_ok {s : State} {base : Addr} (hb : s.gpr .x0 = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block (saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ VG.Impl.Ed25519.AArch64.saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 4096 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_scWith (large := false) hd⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Ed25519.AArch64.ld, VG.Impl.Ed25519.AArch64.saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, VG.Proof.Ed25519.AArch64.word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem out_ok {s : State} {q : Addr} (hq : s.gpr .x1 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x1 0, .str .x .x5 .x1 8, .str .x .x6 .x1 16, .str .x .x7 .x1 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl



theorem saved_output {base q : Addr} {m : Mem} {g : Reg → BitVec 64}
    (hs : Saved base g m) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (w0 w1 w2 w3 : BitVec 64) : Saved base g (st4 m q 0 w0 w1 w2 w3) := by
  have hf : Frame [⟨q,32⟩] m (st4 m q 0 w0 w1 w2 w3) := by
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 0) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 16) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 24) (by decide) (by decide))
  intro rd hr
  have hh : rd.2+8 ≤ 4096 := by
    simp only [VG.Impl.Ed25519.AArch64.saved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  change (st4 m q 0 w0 w1 w2 w3).readW (off base rd.2) 64 = g rd.1
  rw [hf.readW (a := off base rd.2) (w := 64) (r := ⟨base,4096⟩) (Offset.contains_base base hh (by omega))
    (by simp only [List.mem_singleton,forall_eq]; exact hd.symm) (by decide)]
  exact hs rd hr

theorem keeps_kp {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hr : rs ⊆ clob ++ ([.x1,.x19] : List Reg)) : VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hn => h.gpr r (fun hh => hn (hr hh)),h.rd,h.wr⟩

theorem field_kp {base : Addr} {s t : State} (h : Keep base s t) : VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hh => hr (List.mem_append_left _ hh)),h.rd,h.wr⟩


theorem serialize_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block (([.str .x .x4 .x1 0,.str .x .x5 .x1 8,.str .x .x6 .x1 16,.str .x .x7 .x1 24] : List Instr) ++
      saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ VG.Impl.Ed25519.AArch64.saved, t.gpr rd.1 = g rd.1) ∧ VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = leBytes 32 (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Word.out_ok ho hw) fun d de => ?_
  subst d
  have svd := VG.Proof.X25519.AArch64.Word.saved_output hsv hd (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine WP.mono (VG.Proof.X25519.AArch64.Word.restore_ok (s := {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)})
    (g := g) hs.x0 hs.wr svd) fun t ⟨tg,kt⟩ => ?_
  have ko : VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x1,.x19] : List Reg)) s
      {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)} :=
    ⟨fun _ _ => rfl,rfl,rfl⟩
  exact ⟨tg,ko.trans (VG.Proof.X25519.AArch64.Word.keeps_kp kt (by decide)) |>.sub (by decide),by rw [kt.mem,bytesAt_st4]⟩

theorem finish_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : VG.Proof.X25519.AArch64.Word.Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.finish) s fun t =>
      (∀ rd ∈ VG.Impl.Ed25519.AArch64.saved, t.gpr rd.1 = g rd.1) ∧
      VG.Proof.X25519.AArch64.Word.Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = encodeUCoordinate (env s.mem base 1 * env s.mem base 15) := by
  rw [VG.Impl.X25519.AArch64.Word.finish]
  simp only [VG.Impl.X25519.AArch64.Word.freeze,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mul_ok hs (slot_rangeWith (large := false) 1)
    (slot_rangeWith (large := false) 1) (slot_rangeWith (large := false) 15)) fun a ⟨ka,ea⟩ => ?_
  have kma := op_keep (o := 1) ka
  have sva := hsv.outside kma.mem (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freeze_ok (kma.scr hs) (slot_rangeWith (large := false) 1)) fun b ⟨bv,kb⟩ => ?_
  have hb := (kma.scr hs).of_keeps kb (by decide)
  refine WP.mono (VG.Proof.X25519.AArch64.Word.serialize_ok (g := g) hb
    (by rw [kb.gpr _ (by decide),kma.gpr _ (by decide),ho])
    (by rw [kb.wr,kma.wr]; exact hw) hd (by rw [kb.mem]; exact sva)) fun t ⟨tg,kt,rt⟩ => ?_
  refine ⟨tg,?_,?_⟩
  · exact ((VG.Proof.X25519.AArch64.Word.field_kp kma).trans (VG.Proof.X25519.AArch64.Word.keeps_kp kb (by decide))).trans kt |>.sub (by decide)
  · rw [rt,encodeUCoordinate_eq,bv]
    exact congrArg (leBytes 32) (congrArg Fin.val ea)

end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Top`. -/
section

/-! The four-word implementation under the unchanged RFC 7748 signature. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

/-- The shared signature also supplies the non-wrapping scratch range. -/
def localContract : Contract isa :=
  { Proof.X25519.x25519AArch64 with
    pre := fun s => Proof.X25519.x25519AArch64.pre s ∧ (s.gpr .x3).toNat + 4096 ≤ 2^64 }

theorem savedIndices : ∀ rd ∈ VG.Impl.Ed25519.AArch64.saved, ∃ i < 6,
    rd.1 = VG.Impl.X25519.AArch64.saved.getD i .x19 ∧ rd.2 = 8*i := by decide

theorem saved_of_words {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, VG.Proof.Ed25519.AArch64.word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19)) :
    Saved base g m := by
  intro rd hr
  obtain ⟨i,hi,h1,h2⟩ := VG.Proof.X25519.AArch64.Word.savedIndices rd hr
  rw [h1,h2]; exact h i hi

theorem preservedCases : ∀ r ∈ preserved,
    (∃ rd ∈ VG.Impl.Ed25519.AArch64.saved, rd.1 = r) ∨ r ∉ clob ++ ([.x0,.x1,.x19] : List Reg) := by decide

theorem correct {s₀ : State} (hp : localContract.pre s₀) :
    WP isa VG.Impl.X25519.AArch64.Word.x25519 s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ localContract.post s₀ t := by
  have pre := VG.Proof.X25519.AArch64.Pre.of s₀ hp.1
  let base := s₀.gpr .x3
  have hs : VG.Proof.X25519.AArch64.Word.Sc base s₀ := ⟨rfl,by rw [pre.wr]; simp [base,VG.Proof.X25519.AArch64.scR]⟩
  rw [VG.Impl.X25519.AArch64.Word.x25519]
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.setup_ok hs hp.2 rfl rfl
    (by rw [pre.rd]; simp) (by rw [pre.rd]; simp) pre.scalar_sc pre.point_sc)
    fun a ⟨ha,ga,wa,oa,ba,sva,ka⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.ladder_ok ha ga wa ba) fun b ⟨kb,gb,wb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.lastSwap_ok (kb.scratch ha) gb (ladderAfter_swap_le _ _ (by decide)) wb)
    fun c ⟨kc,cx,cz⟩ => ?_)
  have kac := kb.trans kc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.invert_ok (kac.scratch ha)) fun d ⟨kd,di⟩ => ?_)
  have kad := kac.trans (LoopKeep.of_invert kd)
  have od : d.gpr .x1 = s₀.gpr .x0 := (kad.gpr _ (by decide) (by decide)).trans oa
  have svd : Saved base s₀.gpr d.mem := (VG.Proof.X25519.AArch64.Word.saved_of_words sva).outside kad.mem (by decide)
  have dx : env d.mem base 1 = env c.mem base 1 := by
    exact congrArg toFe (kd.mem.fe (Or.inl (by decide : offset 1+32 ≤ 512)) (by decide))
  refine WP.mono (VG.Proof.X25519.AArch64.Word.finish_ok (kad.scratch ha) od
    (by rw [kad.wr,ka.wr,pre.wr]; simp) pre.out_sc svd) fun t ⟨tg,kt,rt⟩ => ?_
  refine ⟨fun r hr => ?_,?_⟩
  · rcases VG.Proof.X25519.AArch64.Word.preservedCases r hr with ⟨rd,hrd,er⟩ | hn
    · rw [← er]; exact tg rd hrd
    · have kk := (ka.trans kad.kp).trans kt
      exact kk.sub (by decide) |>.gpr r hn
  · change bytesAt t.mem (s₀.gpr .x0) 32 = Spec.X25519.x25519
      (bytesAt s₀.mem (s₀.gpr .x1) 32) (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [rt,dx,di,cx,cz,x25519_eq]

theorem x25519_ok (s : State) (hs : localContract.pre s) :
    ∃ tr t, Exec isa VG.Impl.X25519.AArch64.Word.x25519 s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr,t,he,hg,hp⟩ := VG.Proof.X25519.AArch64.Word.correct hs
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he (by lit_decide)⟩,hp⟩
end VG.Proof.X25519.AArch64.Word

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Word.Verified`. -/
section

/-! Correctness, constant time, and the original shared contract. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64

theorem x25519_ct : ConstantTime isa localContract.pre localContract.pub
    Impl.X25519.AArch64.Word.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => VG.Proof.X25519.AArch64.agree₀ hp) (by taint_decide)

theorem x25519_verified : Verified AArch64.target Impl.X25519.AArch64.Word.x25519
    (Spec.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.X25519.AArch64.Word.x25519_ok VG.Proof.X25519.AArch64.Word.x25519_ct (by
    sig_implies [Spec.X25519.x25519Contract,Spec.X25519.x25519Sig,AArch64.abi,AArch64.argRegs,
      VG.Proof.X25519.AArch64.Word.localContract,Proof.X25519.x25519AArch64] [VG.Proof.X25519.AArch64.sat]
      using VG.Proof.X25519.AArch64.sat)
end VG.Proof.X25519.AArch64.Word

end
