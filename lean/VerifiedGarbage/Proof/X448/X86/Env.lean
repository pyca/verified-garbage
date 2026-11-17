module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.X448.X86.FnContract
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.X86.Copy
public import VerifiedGarbage.Proof.X448.X86.Swap
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `X448.X86.FieldCall`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): calls of the field functions

`call3 f body o a b` and `call2 f body o a` (`Impl/X448/X86.lean`) push the
offsets and `ws = edi` and call the field function `f`, whose code is `body`
(`call3_ok`, `call2_ok`, through the function's own lemma, `Fn.lean`). From a
state whose working space is at `edi` (`Scr`) and lies apart from the 20
bytes of stack below `esp` that the call uses (`CallCtx`), a call changes
only `eax`, `ecx` and `edx`, the result at `o`, the functions' own working
space and that stack (`COp`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The stack a call uses: its arguments and return address. -/
abbrev callStk (s : State) : Region := below (s.gpr .esp) 20

/-- What a call of a field function needs of the stack. -/
structure CallCtx (s : State) (base : Addr) : Prop where
  sp : 20 ≤ (s.gpr .esp).toNat
  sep : Region.Disjoint ⟨base, 8192⟩ (callStk s)

/-- What a call of a field function writing `o` changes. -/
structure COp (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps [.eax, .ecx, .edx] s t
  mem : WsField base o s.mem t.mem
  ext : Frame [⟨base, 8192⟩, callStk s] s.mem t.mem

theorem CallCtx.keep {s t : State} {base : Addr} (h : CallCtx s base) (hsp : t.gpr .esp = s.gpr .esp) :
    CallCtx t base := ⟨hsp ▸ h.sp, by simp only [callStk, hsp]; exact h.sep⟩

/-- Byte `d` of the stack a call uses. -/
theorem callStk_byte (s : State) {d : Nat} (hd : d < 20) :
    (callStk s).Contains ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 + BitVec.ofNat 64 d) 1 :=
  Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- A byte of the stack a call uses lies outside the working space. -/
theorem CallCtx.out {s : State} {base : Addr} (h : CallCtx s base) {d : Nat} (hd : d < 20) :
    8192 ≤ ofs base ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 + BitVec.ofNat 64 d) :=
  not_contains_ofs fun hw => h.sep _ hw (callStk_byte s hd)

/-- Memory the same in the working space. -/
def WsEq (base : Addr) (m m' : Mem) : Prop := ∀ x, ofs base x < 8192 → m' x = m x

theorem WsEq.of_frame {s : State} {base : Addr} (h : CallCtx s base) {m m' : Mem}
    (hf : Frame [callStk s] m m') : WsEq base m m' := fun x hx =>
  hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun hc => h.sep x (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith) hc

theorem WsEq.limbs {base : Addr} {m m' : Mem} (h : WsEq base m m') {d : Nat} (hd : d + 112 ≤ 8192)
    {i : Nat} (hi : i < 28) : limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (Mem.readW_congr fun k hk => (h _ (by rw [ofs_off base (by omega_arith)]; omega_arith)).symm).symm

theorem WsEq.fe {base : Addr} {m m' : Mem} (h : WsEq base m m') {d : Nat} (hd : d + 112 ≤ 8192) :
    fe m' base d = fe m base d := valN_congr fun _ hi => h.limbs hd hi

theorem WsEq.bounded {base : Addr} {m m' : Mem} (h : WsEq base m m') {d : Nat} (hd : d + 112 ≤ 8192)
    (hb : Bounded m base d) : Bounded m' base d := fun i hi => by rw [h.limbs hd hi]; exact hb i hi

theorem WsEq.field {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h : WsEq base m₁ m₂)
    (hf : FieldMem base o m₂ m₃) : WsField base o m₁ m₃ :=
  fun x h8 hx hw => (hf x hx hw).trans (h x h8)

/-- The return address of a function entered as `t` lies outside the working space. -/
theorem ret_disjoint {t : State} {base : Addr} (h : ∀ k < 4, 8192 ≤ ofs base ((t.gpr .esp).setWidth 64 + BitVec.ofNat 64 k)) :
    Region.Disjoint ⟨(t.gpr .esp).setWidth 64, 4⟩ ⟨base, 8192⟩ := by
  intro x hx hw
  simp only [Region.Contains] at hx hw
  have := h (x - (t.gpr .esp).setWidth 64).toNat (by omega_arith)
  rw [show (t.gpr .esp).setWidth 64 + BitVec.ofNat 64 (x - (t.gpr .esp).setWidth 64).toNat = x by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]; exact BitVec.sub_add_cancel _ _] at this
  simp only [ofs] at this
  omega_arith

/-- A byte at an offset below `esp`, as a byte of the stack a call uses. -/
theorem stk_addr {E : BitVec 32} (hE : 20 ≤ E.toNat) {m d : Nat} (hm : m ≤ 20) :
    (E - BitVec.ofNat 32 m).setWidth 64 + BitVec.ofNat 64 d =
      (E - BitVec.ofNat 32 20).setWidth 64 + BitVec.ofNat 64 (20 - m + d) := by
  rw [VG.X86.Taint.sub_setWidth (by omega_arith), VG.X86.Taint.sub_setWidth hE]
  have := E.isLt
  bv_omega

/-- Argument `i` of a call with `n` arguments pushed, in the stack the call uses. -/
theorem argAddr_pushed {rs : List Reg} {s : State} (hE : 20 ≤ (s.gpr .esp).toNat) (hl : rs.length ≤ 4)
    {rd wr : List Region} {i : Nat} (hi : i < rs.length) :
    argAddr ((pushed rs s).callEntry.withRegions rd wr) i =
      (s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 + BitVec.ofNat 64 (4 * i) := by
  change argAddr (pushed rs s).callEntry i = _
  rw [argAddr_callEntry, pushed_esp]
  exact addr_eq (by rw [sub_toNat (by omega_arith)]; have := (s.gpr .esp).isLt; omega_arith)

/-- A call of a field function whose code is `body`, with `rs` pushed as its
arguments, the first of which (pushed last) is the working space. -/
theorem callFrame_ok {name : String} {body : Prog isa} (hn : NoSp body) (h0 : stackUse body = 0)
    {rs : List Reg} (hrs : .esp ∉ rs) (hl3 : 3 ≤ rs.length) (hl4 : rs.length ≤ 4)
    {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) {v : Nat → BitVec 32}
    (hv : ∀ i < rs.length, arg (pushed rs s).callEntry i = v i) (h0v : v 0 = s.gpr .edi)
    (h1v : v 1 = BitVec.ofNat 32 o) (h2v : v 2 = BitVec.ofNat 32 a) {Q : Mem → Mem → Prop}
    (hok : ∀ t, FnEntry t base rs.length o a → (∀ i < rs.length, arg t i = v i) →
      WsEq base s.mem t.mem → t.wr = [⟨base, 8192⟩] →
      WP isa body t fun t' => FnOut base o t t' ∧ Q t.mem t'.mem) :
    WP isa (.frame (.push rs) (.call name body) (.pop .eax rs.length)) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ ∃ m, WsEq base s.mem m ∧ Q m t.mem := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  have hE := hc.sp
  have hne : rs ≠ [] := fun h => by rw [h] at hl3; simp at hl3
  let rd : List Region := [below (s.gpr .esp) (4 * rs.length)]
  let wr : List Region := [⟨base, 8192⟩]
  let e := (pushed rs s).callEntry.withRegions rd wr
  have esp_e : e.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) := callEntry_esp' rs s
  have frame_e : Frame [below (s.gpr .esp) (4 * rs.length + 4)] s.mem e.mem :=
    callEntry_frame (by omega_arith) hrs
  have stk : below (s.gpr .esp) (4 * rs.length + 4) ∈ [callStk s] ∨ 4 * rs.length + 4 < 20 := by
    rcases Nat.lt_or_ge rs.length 4 with h | h
    · exact Or.inr (by omega_arith)
    · exact Or.inl (by rw [show rs.length = 4 by omega_arith]; exact List.mem_singleton_self _)
  have weq : WsEq base s.mem e.mem := WsEq.of_frame hc (frame_e.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    refine ⟨callStk s, List.mem_singleton_self _, below_sub (by omega_arith) hE⟩)
  have entry : FnEntry e base rs.length o a := by
    refine ⟨?_, List.mem_singleton_self _, ?_, ⟨fun i hi => ?_, fun i hi k hk => ?_⟩, hl3,
      fun k hk => ?_, ?_, ?_, ho, ha⟩
    · change (arg (pushed rs s).callEntry 0).setWidth 64 = _
      rw [hv 0 (by omega_arith), h0v]; exact hs.edi
    · change (arg (pushed rs s).callEntry 0).toNat + 8192 ≤ _
      rw [hv 0 (by omega_arith), h0v]; exact hs.nowrap
    · refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      rw [argAddr_pushed hE hl4 hi]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [argAddr_pushed hE hl4 hi, Offset.add_add, stk_addr hE (by omega_arith)]
      exact hc.out (by omega_arith)
    · rw [esp_e, stk_addr (d := k) hE (by omega_arith)]
      exact hc.out (by omega_arith)
    · change arg (pushed rs s).callEntry 1 = _; rw [hv 1 (by omega_arith), h1v]
    · change arg (pushed rs s).callEntry 2 = _; rw [hv 2 (by omega_arith), h2v]
  let K : Contract isa :=
    { pre := fun t => t = e
      post := fun t t' => FnOut base o t t' ∧ Q t.mem t'.mem
      pub := fun _ _ => True }
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa body t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    rintro t rfl
    obtain ⟨tr, t', ex, out, q⟩ := hok e entry (fun i hi => hv i hi) weq rfl
    refine ⟨tr, t', ex, out.abi hn h0 ex ?_, out, q⟩
    intro r hr
    rw [show e.wr = wr from rfl] at hr
    rw [List.mem_singleton.mp hr]
    exact ret_disjoint entry.ret
  refine WP.callWith (k := K) hK hn hne hrs (by rw [h0]; omega_arith)
    ⟨rfl, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ fun s' hrd hwr hcs hfr ⟨s₂, hm2, hpost, hq⟩ => ?_
  · rcases List.mem_append.mp hr with hr | hr
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr
  refine ⟨⟨⟨fun r hr => ?_, hrd, hwr⟩, ?_, ?_⟩, ?_, e.mem, weq, by rw [← hm2]; exact hq⟩
  · have : r ∈ calleeSaved := by
      cases r <;> first | decide | exact absurd (by decide) hr
    exact hcs r this
  · rw [← hm2]; exact weq.field hpost.mem
  · rw [h0] at hfr
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨callStk s, by simp, below_sub (by omega_arith) hE⟩
  · rw [← hm2]; exact hpost.bounded

theorem COp.of_movs {base : Addr} {o : Nat} {s s₁ t : State} (k : Keeps [.eax, .ecx, .edx] s s₁)
    (hm : s₁.mem = s.mem) (h : COp base o s₁ t) : COp base o s t := by
  have esp : s₁.gpr .esp = s.gpr .esp := k.1 _ (by decide)
  exact ⟨k.trans h.keeps, by rw [← hm]; exact h.mem, by rw [← hm, callStk, ← esp]; exact h.ext⟩

/-- A call of a binary field function whose code is `body`. -/
theorem call3_ok {name : String} {body : Prog isa} (hn : NoSp body) (h0 : stackUse body = 0)
    {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b)
    {op : Spec.X448.Fe → Spec.X448.Fe → Spec.X448.Fe}
    (hok : ∀ t, FnEntry t base 4 o a → arg t 3 = BitVec.ofNat 32 b → Bounded t.mem base a →
      Bounded t.mem base b → WP isa body t fun t' =>
        FnOut base o t t' ∧ F t'.mem base o = op (F t.mem base a) (F t.mem base b)) :
    WP isa (call3 name body o a b) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = op (F s.mem base a) (F s.mem base b) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  unfold call3
  rw [WP.seq_iff]
  refine wp_mov rfl fun s₁ u₁ => wp_mov rfl fun s₂ u₂ => wp_mov rfl fun s₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s s₃ :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hs₃ := hs.of_keeps k₃ (by decide)
  have hc₃ := hc.keep (k₃.1 _ (by decide))
  have fit : 4 * [Reg.edx, .ecx, .eax, .edi].length + 4 ≤ (s₃.gpr .esp).toNat := hc₃.sp
  have av : ∀ i (hi : i < 4), arg (pushed [.edx, .ecx, .eax, .edi] s₃).callEntry i =
      s₃.gpr [Reg.edx, .ecx, .eax, .edi][4 - 1 - i] := fun i hi => callEntry_arg fit (by decide) hi
  have v1 : s₃.gpr .eax = BitVec.ofNat 32 o := (u₃.other _ (by decide)).trans ((u₂.other _ (by decide)).trans u₁.gpr)
  have v2 : s₃.gpr .ecx = BitVec.ofNat 32 a := (u₃.other _ (by decide)).trans u₂.gpr
  refine WP.mono (callFrame_ok (rs := [.edx, .ecx, .eax, .edi]) (name := name) hn h0 (by decide) (by decide)
    (by decide) hs₃ hc₃ ho ha (v := fun i => arg (pushed [.edx, .ecx, .eax, .edi] s₃).callEntry i)
    (fun _ _ => rfl) (av 0 (by decide)) ((av 1 (by decide)).trans v1) ((av 2 (by decide)).trans v2)
    (Q := fun m m' => F m' base o = op (F m base a) (F m base b))
    fun t he hav hw _ => hok t he (by rw [hav 3 (by decide), av 3 (by decide)]; exact u₃.gpr)
      (hw.bounded (by omega_arith) (m₃ ▸ ab)) (hw.bounded (by omega_arith) (m₃ ▸ bb)))
    fun t ⟨hop, hbd, m, hm, hq⟩ => ⟨hop.of_movs k₃ m₃, hbd, ?_⟩
  rw [hq, F, F, hm.fe (by omega_arith), hm.fe (by omega_arith), m₃]

/-- A call of `vg_gf448_r16_mul_a24`'s code `body`. -/
theorem call2_ok {name : String} {body : Prog isa} (hn : NoSp body) (h0 : stackUse body = 0)
    {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) {op : Spec.X448.Fe → Spec.X448.Fe}
    (hok : ∀ t, FnEntry t base 3 o a → Bounded t.mem base a → WP isa body t fun t' =>
        FnOut base o t t' ∧ F t'.mem base o = op (F t.mem base a)) :
    WP isa (call2 name body o a) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = op (F s.mem base a) := by
  have ha' : a + 112 ≤ 3584 := ha
  unfold call2
  rw [WP.seq_iff]
  refine wp_mov rfl fun s₁ u₁ => wp_mov rfl fun s₂ u₂ => WP.block_nil ?_
  have k₂ : Keeps [.eax, .ecx, .edx] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hc₂ := hc.keep (k₂.1 _ (by decide))
  have fit : 4 * [Reg.ecx, .eax, .edi].length + 4 ≤ (s₂.gpr .esp).toNat := by have := hc₂.sp; simp; omega_arith
  have av : ∀ i (hi : i < 3), arg (pushed [.ecx, .eax, .edi] s₂).callEntry i =
      s₂.gpr [Reg.ecx, .eax, .edi][3 - 1 - i] := fun i hi => callEntry_arg fit (by decide) hi
  refine WP.mono (callFrame_ok (rs := [.ecx, .eax, .edi]) (name := name) hn h0 (by decide) (by decide)
    (by decide) hs₂ hc₂ ho ha (v := fun i => arg (pushed [.ecx, .eax, .edi] s₂).callEntry i)
    (fun _ _ => rfl) (av 0 (by decide)) ((av 1 (by decide)).trans ((u₂.other _ (by decide)).trans u₁.gpr))
    ((av 2 (by decide)).trans u₂.gpr)
    (Q := fun m m' => F m' base o = op (F m base a))
    fun t he _ hw _ => hok t he (hw.bounded (by omega_arith) (m₂ ▸ ab)))
    fun t ⟨hop, hbd, m, hm, hq⟩ => ⟨hop.of_movs k₂ m₂, hbd, ?_⟩
  rw [hq, F, F, hm.fe (by omega_arith), m₂]

theorem mulCall_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (mulCall o a b) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b :=
  call3_ok (op := (· * ·)) (NoSp.of_all (by lit_decide)) (by lit_decide) hs hc ho ha hb ab bb
    fun _ he hvb ab' bb' => mulFn_ok he hvb hb ab' bb'

theorem addCall_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (addCall o a b) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b :=
  call3_ok (op := (· + ·)) (NoSp.of_all (by lit_decide)) (by lit_decide) hs hc ho ha hb ab bb
    fun _ he hvb ab' bb' => addFn_ok he hvb hb ab' bb'

theorem subCall_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (subCall o a b) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b :=
  call3_ok (op := (· - ·)) (NoSp.of_all (by lit_decide)) (by lit_decide) hs hc ho ha hb ab bb
    fun _ he hvb ab' bb' => subFn_ok he hvb hb ab' bb'

theorem a24Call_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (a24Call o a) s fun t =>
      COp base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a :=
  call2_ok (op := (Spec.X448.a24 * ·)) (NoSp.of_all (by lit_decide)) (by lit_decide) hs hc ho ha ab
    fun _ he ab' => mulA24Fn_ok he ab'

/-- What code that never writes `esp` changes in memory, alongside what a
proof of it states: only its writable regions and the stack it uses. -/
theorem WP.withFrame {c : Prog isa} (hc : NoSp c) {s : State} (hd : stackUse c ≤ (s.gpr .esp).toNat)
    {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem t.mem :=
  let ⟨tr, t, ex, q⟩ := h
  ⟨tr, t, ex, q, VG.X86.Exec.frameSp ex hc hd⟩

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): the working space as field-element slots

Field operations update one of twenty-two slots, preserving bounded limbs in
every slot. The frame excludes saved registers, the swap bit and the scalar's
decoded bits.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

def workRegs : List Reg := .edx :: clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : Keeps workRegs s t
  mem : WsOut2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨Keeps.refl _ _, WsOut2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (h' : Keep base t u) :
    Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega_using []

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 112 ≤ slot j.val ∨ slot j.val + 112 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega_using [hn]

theorem Op.keep {base : Addr} {o : Index} {s t : State} (h : Op base (slot o.val) s t) : Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p _ hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega_using [hp]

theorem COp.keep {base : Addr} {o : Index} {s t : State} (h : COp base (slot o.val) s t) : Keep base s t := by
  refine ⟨h.keeps.mono (by decide), ?_⟩
  intro p h8 hp hq
  apply h.mem p h8 _ hq
  have := o.isLt
  simp only [slot]
  omega_using [hp]

theorem Keep.ctx {base : Addr} {s t : State} (h : Keep base s t) (hc : CallCtx s base) : CallCtx t base :=
  hc.keep (h.regs.1 _ (by decide))

theorem E_update {base : Addr} {m m' : Mem} {o : Index} (h : WsField base (slot o.val) m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    rw [h.fe (slot_sep hi) (slot_bound i)]

theorem bounded_update {base : Addr} {m m' : Mem} {o : Index} (h : WsField base (slot o.val) m m')
    (hm : BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (slot_sep hi) (slot_bound i) hj]
    exact hm i j hj

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (o a b : Index) :
    WP isa (mulCall (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opMul o a b (E s.mem base) :=
  WP.mono (mulCall_ok hs hc (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (o a b : Index) :
    WP isa (addCall (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (addCall_ok hs hc (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (o a b : Index) :
    WP isa (subCall (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSub o a b (E s.mem base) :=
  WP.mono (subCall_ok hs hc (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (o a : Index) :
    WP isa (a24Call (slot o.val) (slot a.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opA24 o a (E s.mem base) :=
  WP.mono (a24Call_ok hs hc (slot_bound o) (slot_bound a) (hb a)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (copy (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opCopy o a (E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 112 ≤ slot a.val ∨ slot a.val + 112 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (copy_ok hs (Nat.le_trans (slot_bound o) (by decide))
    (Nat.le_trans (slot_bound a) (by decide)) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update (op.mem.ws (by decide)) hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [E_update (op.mem.ws (by decide)), show F t.mem base (slot o.val) = F s.mem base (slot a.val) from
      congrArg toFe (valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .ebx = mask sw) :
    WP isa (.block (cswap (slot x.val) (slot y.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ t.gpr .ebx = s.gpr .ebx ∧
      E t.mem base = opSwap x y sw (E s.mem base) := by
  refine WP.mono (cswap_ok hs (slot_bound x) (slot_bound y) (slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : Index, i ≠ x → i ≠ y → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := slot_sep hix
    have ey := slot_sep hiy
    have hi := slot_bound i
    change (word t.mem base (slot i.val + 4 * j)).toNat = _
    rw [tm.word (by omega_using [hj, ex]) (by omega_using [hj, ey]) (by change slot i.val + 112 ≤ 3584 at hi; omega_using [hj, hi])]
  have fx : E t.mem base x = if sw then E s.mem base y else E s.mem base x := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact tx
  have fy : E t.mem base y = if sw then E s.mem base x else E s.mem base y := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p _ hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega_using [hp]
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg toFe (valN_congr (other i hix hiy))

end VG.Proof.X448.X86
