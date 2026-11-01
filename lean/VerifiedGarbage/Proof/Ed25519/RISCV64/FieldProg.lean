module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ed25519
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Reduce
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base

/-!
# Ed25519 on RISC-V: field programs

The slots as residues (`env`), what an operation does to them (`evalOp`),
and the code of a list of operations doing that (`fieldCode_ok`), keeping
every register but `fclob` and every byte outside the field area `FA`
(`Keep`). A call of `vg_gf25519_r32_mul` (`mulCall_ok`) is the inlined
product's equal, for a working space whose 4096 bytes are writable (`WS`)
and whose address is a multiple of 8 (`Ctx`). The extended Edwards addition
of the slots is `Spec.Ed25519.pointAdd` (`pointAdd_eval`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.X448.RISCV64.R64 (clob64)
open VG.Proof.X25519 (val32_congr)

abbrev Env := Slot → Spec.X25519.Fe

/-- The slots' elements. -/
def env (m : Mem) (b : Addr) : Env := fun i => FS m b (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b | .mulc o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

/-- The registers field code writes: X25519's, and those of a call of the product (`a0`–`a2`,
the link registers). -/
abbrev fclob : List Reg := [.ra, .a0, .a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- The working space's first 4096 bytes are writable. -/
abbrev WS (b : Addr) (s : State) : Prop := Covers [⟨b, 4096⟩] s.wr

theorem WS.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : WS b s) (hr : Rest ws s s') : WS b s' := by
  unfold WS; rw [hr.wr]; exact h

structure Keep (b : Addr) (s s' : State) : Prop where
  rest : Rest fclob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : Addr) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : Addr} {s t u : State} (h : Keep b s t) (k : Keep b t u) : Keep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : Addr} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

/-- An operation's frame: the result's slot and the product's limbs. -/
abbrev opFrame (b : Addr) (o : Nat) : List Region :=
  [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

/-- The other slots, through writes of the slot `o` and of bytes from 768 up. -/
theorem slot_frame {b : Addr} {m m' : Mem} {o i : Slot} (hne : i ≠ o) {e k : Nat} (he : 768 ≤ e)
    (hk : e + k ≤ 2048) (hf : Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩, ⟨b + BitVec.ofNat 64 e, k⟩] m m') :
    FS m' b (offset i) = FS m b (offset i) := by
  have hi := slot_range i
  have ho := slot_range o
  have hsep : offset i + 32 ≤ offset o ∨ offset o + 32 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega
  refine congrArg Proof.X25519.toFe (val32_congr (limb_frame hf fun r hr k hk => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

theorem field_update {b : Addr} {m m' : Mem} (o : Slot) {e k : Nat} (he : 768 ≤ e) (hk : e + k ≤ 2048)
    (hf : Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩, ⟨b + BitVec.ofNat 64 e, k⟩] m m') :
    env m' b = Function.update (env m b) o (FS m' b (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp only [Function.update_self, env]
  · rw [Function.update_of_ne hi]
    exact slot_frame hi he hk hf

theorem frame_FA {b : Addr} {o : Slot} {e k : Nat} (he : 64 ≤ e) (hk : e + k ≤ 1024) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩, ⟨b + BitVec.ofNat 64 e, k⟩] m m') :
    Frame [FA b] m m' := by
  have ho := slot_range o
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega) (by omega)
  · exact Offset.sub _ (by omega) (by omega)

theorem frame_o {b : Addr} {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m m') :
    Frame (opFrame b o) m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem field_finish {b : Addr} {s t : State} (o : Slot) (hr : Rest fclob s t)
    (hf : Frame (opFrame b (offset o)) s.mem t.mem) {v : Spec.X25519.Fe}
    (hv : FS t.mem b (offset o) = v) :
    Keep b s t ∧ env t.mem b = Function.update (env s.mem b) o v := by
  have hA := eACC_eq
  rw [← hv]
  exact ⟨⟨hr, frame_FA (by omega) (by omega) hf⟩, field_update o (by omega) (by omega) hf⟩

/-! ## A call of the product -/

/-- An element at an offset of the working space, as `valAt` reads it. -/
theorem valAt_slot (m : Mem) (b : Addr) (i : Slot) :
    Spec.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), V, V]
  exact val32_congr fun k _ => by rw [limb, limb, wd_shift, Nat.zero_add]

/-- What a call of `vg_gf25519_r32_mul` asks of the function: the working space's first 4096
bytes, aligned, and the offsets of `o`, `a` and `c` in `a1`–`a3`. -/
def mulK (b : Addr) (o a c : Slot) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨b, 4096⟩] ∧ t.gpr .a0 = b ∧ b.toNat % 8 = 0 ∧
    offArg t .a1 = BitVec.ofNat 32 (offset o) ∧ offArg t .a2 = BitVec.ofNat 32 (offset a) ∧
    offArg t .a3 = BitVec.ofNat 32 (offset c)
  post t t' := Frame [FA b] t.mem t'.mem ∧
    env t'.mem b = Function.update (env t.mem b) o (env t.mem b a * env t.mem b c)
  pub _ _ := True

theorem fits_slot (i : Slot) : Spec.X25519.Field32.Fits (BitVec.ofNat 32 (offset i)) := by
  have := slot_range i
  simp only [Spec.X25519.Field32.Fits, Spec.X25519.Field32.elemBytes, Spec.X25519.Field32.ownAt,
    BitVec.toNat_ofNat]
  omega

theorem mulK_ok {b : Addr} (o a c : Slot) :
    ∀ t, (mulK b o a c).pre t → ∃ tr t', VG.Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧
      (mulK b o a c).post t t' := fun t ⟨hrd, hwr, h0, hal, t1, t2, t3⟩ => by
  have ho := slot_range o
  obtain ⟨tr, t', he, ⟨hV, hF⟩, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t2, .t3, .t4, .t5, .t6]
    (mulFn_ok hrd (by rw [hwr, h0]) (by rw [t1]; exact fits_slot o) (by rw [t2]; exact fits_slot a)
      (by rw [t3]; exact fits_slot c) (by rw [h0]; exact hal)) (by decide +kernel)
  refine ⟨tr, t', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_⟩
  rw [h0, t1, t2, t3, valAt_slot, valAt_slot, valAt_slot] at hV
  rw [h0, t1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hF
  have hF' : Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩, ⟨b + BitVec.ofNat 64 768, 256⟩] t.mem t'.mem :=
    hF.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h]
  exact ⟨frame_FA (by omega) (by omega) hF',
    (field_update o (by omega) (by omega) hF').trans (congrArg _ (Proof.X25519.toFe_mul hV))⟩

theorem low_word (v : Nat) (hv : v < 2 ^ 32) : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega), Nat.mod_eq_of_lt hv]

/-- **A call of `vg_gf25519_r32_mul`**, as the inlined product. -/
theorem mulCall_ok {b : Addr} {s : State} (hc : Ctx b s) (hw : WS b s) (o a c : Slot) :
    WP isa (mulCall (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  unfold mulCall
  refine WP.seq (wp_mv fun s1 u1 => wp_li (by omega) fun s2 u2 =>
    wp_li (by omega) fun s3 u3 => wp_li (by omega) fun s4 u4 => WP.block_nil ?_)
  have hr4 : Rest [.a0, .a1, .a2, .a3] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have e0 : s4.gpr .a0 = b := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.a3]
  have e1 : s4.gpr .a1 = BitVec.ofNat 64 (offset o) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
  have e2 : s4.gpr .a2 = BitVec.ofNat 64 (offset a) := by rw [u4.other _ (by decide), u3.gpr]
  have e3 : s4.gpr .a3 = BitVec.ofNat 64 (offset c) := u4.gpr
  have g : ∀ q, q ∉ linkRegs → (s4.callEntry.withRegions [] [⟨b, 4096⟩]).gpr q = s4.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hw4 : Covers [⟨b, 4096⟩] s4.wr := hw.of_rest hr4
  refine WP.seq (WP.call (k := mulK b o a c) (mulK_ok o a c) (rd := []) (wr := [⟨b, 4096⟩])
    ⟨rfl, rfl, by rw [g _ (by decide)]; exact e0, hc.al,
      by rw [offArg, g _ (by decide), e1]; exact low_word _ (by omega),
      by rw [offArg, g _ (by decide), e2]; exact low_word _ (by omega),
      by rw [offArg, g _ (by decide), e3]; exact low_word _ (by omega)⟩
    (by rw [List.nil_append]; exact hw4.right) hw4 ?_ (by decide +kernel))
  intro t hrd hwr hsp _ _ hg ⟨hF, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hV
  rw [hm4] at hF hV
  have ha0 : t.gpr .a0 = b := by rw [hg _ (by decide) (by decide +kernel), e0]
  refine wp_mv fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · by_cases h3 : q = .a3
    · subst h3
      rw [v1.gpr, ha0, hc.a3]
    · have hl : q ∉ linkRegs := by revert hq; cases q <;> decide
      have hd : ∀ i ∈ instrs mulFn, dstOf i ≠ some q := by
        revert hq h3; cases q <;> first | decide +kernel | (intro h; exact absurd (by decide) h)
      rw [v1.other _ h3, hg _ hl hd, hr4.gpr _ (by revert hq h3; cases q <;> decide)]
  · rw [v1.rd, hrd, hr4.rd]
  · rw [v1.wr, hwr, hr4.wr]
  · rw [v1.sp, hsp, hr4.sp]
  · rw [v1.mem]; exact hF
  · rw [v1.mem]; exact hV

/-! ## Operations and programs -/

theorem fieldOp_ok {b : Addr} {s : State} (hc : Ctx b s) (hw : WS b s) (op : FieldOp) :
    WP isa op.code s fun t => Keep b s t ∧ env t.mem b = evalOp op (env s.mem b) := by
  have hA := eACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.mulAt_ok (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) hf (Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc hw o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.add_ok (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.sub_ok (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : Addr} (hc : Ctx b s) (hw : WS b s) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (fieldOp_ok hc hw op) fun t ⟨ht, et⟩ => ?_)
    refine WP.mono (ih (ht.ctx hc) (hw.of_rest ht.rest)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-! ## Inline programs, framed by the slots they write -/

/-- The slot an operation writes. -/
def opOut : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o

/-- An inline operation changes no register but the field code's `clob64`, and no memory but its result
and the product's limbs. -/
theorem fieldOpW_ok {b : Addr} {s : State} (hc : Ctx b s) (op : FieldOp) (hi : op.inline = true) :
    WP isa op.code s fun t => Rest clob64 s t ∧ Frame (opFrame b (offset (opOut op))) s.mem t.mem ∧
      env t.mem b = evalOp op (env s.mem b) := by
  have hA := eACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (by omega) (by omega) (frame_o hf), hv]; rfl
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (by omega) (by omega) (frame_o hf), hv]; rfl
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.mulAt_ok (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc) fun t ⟨hr, hf, hv⟩ => ⟨hr, hf, ?_⟩
    rw [field_update o (by omega) (by omega) hf]; exact congrArg _ (Proof.X25519.toFe_mul hv)
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.add_ok (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (by omega) (by omega) (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (R64.sub_ok (by omega) (by omega) (by omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (by omega) (by omega) (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_sub hv)

/-- Inline field code, framed by any regions `R` that hold the results and the product's limbs. -/
theorem fieldCodeW_ok (ops : List FieldOp) (hi : ops.all FieldOp.inline = true) {b : Addr}
    (R : List Region) (hR : ∀ op ∈ ops, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ R, r.Sub r')
    {s : State} (hc : Ctx b s) :
    WP isa (fieldCode ops) s fun t =>
      Rest clob64 s t ∧ Frame R s.mem t.mem ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, rfl⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hi
    refine WP.seq (WP.mono (fieldOpW_ok hc op hi.1) fun t ⟨rt, ft, et⟩ => ?_)
    refine WP.mono (ih hi.2 (fun op' h' => hR op' (List.mem_cons_of_mem _ h')) (hc.of_rest rt (by decide)))
      fun u ⟨ru, fu, eu⟩ => ⟨rt.trans ru, (ft.sub (hR op List.mem_cons_self)).trans fu, by rw [eu, et]; rfl⟩

/-! ## The addition formula -/

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

/-- The sum of the points at slots 0–3 and 4–7, as the formula computes it. -/
def addResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 5 - e 4)
  let b := (e 1 + e 0) * (e 5 + e 4)
  let c := (e 3 * e 16 + e 3 * e 16) * e 7
  let dd := (e 2 + e 2) * e 6
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) : point (evalOps pointAddOps e) 0 1 2 3 = addResult e := rfl

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) := by
  rw [pointAdd_formula]
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

end VG.Proof.Ed25519.RISCV64
