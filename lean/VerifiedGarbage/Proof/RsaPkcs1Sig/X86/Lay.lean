module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The x86 RSA padding functions: where everything is

`Lay`: what two runs share of where things are: the frame's base `B` (the
stack pointer in the body), its size `F`, the bytes `A` of the arguments,
the arguments `argv`, and the buffers the function only reads (`ro`) and
writes (`rw`). Above the frame are the push of the callee-saved registers
and the return address (`TOP`, `Impl/RsaPkcs1Sig/X86/Wrap.lean`) and the
arguments (`ARGS`); below it, the `C` bytes the calls' frames use (`LOW`).

`Lay.Ok L σ`: the state `σ` the body starts from has that layout.
`Lay.St L σ s`: a state of the body: `σ`'s stack pointer and permissions,
and memory changed only within the frame, the writable buffers and `LOW`
(`W`). The arguments stay as they were (`St.arg`), and so do the buffers
only read (`St.ro`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86 VG.X86.Wp

structure Lay where
  B : BitVec 32
  F : Nat
  argv : List (BitVec 32)
  ro : List Region
  rw : List Region
  C : Nat

namespace Lay

variable (L : Lay)

abbrev Q : Addr := L.B.setWidth 64
abbrev fr (d : Nat) : Addr := L.Q + BitVec.ofNat 64 d
abbrev A : Nat := 4 * L.argv.length
abbrev FR : Region := ⟨L.Q, L.F⟩
abbrev SAVE : Region := ⟨L.fr L.F, 16⟩
abbrev RET : Region := ⟨L.fr (L.F + 16), 4⟩
abbrev ARGS : Region := ⟨L.fr (L.F + 20), L.A⟩
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.C, L.C⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.C, L.C + L.F + 16⟩
/-- What the body may write. -/
abbrev W : List Region := L.FR :: L.rw ++ [L.LOW]
/-- Argument `j`'s place. -/
abbrev argA (j : Nat) : Addr := L.fr (Impl.RsaPkcs1Sig.X86.argOff L.F j)

structure Ok (σ : State) : Prop where
  sp : σ.gpr .esp = L.B
  rd : σ.rd = L.ro
  wr : σ.wr = L.FR :: L.SAVE :: (L.rw ++ [L.ARGS])
  BC : L.C ≤ L.B.toNat
  fit : L.B.toNat + L.F + 20 + L.A ≤ 2 ^ 32
  stk : ∀ r ∈ L.ro ++ L.rw, L.STK.Disjoint r
  ret : ∀ r ∈ L.rw, L.RET.Disjoint r
  wro : ∀ w ∈ L.rw, ∀ r ∈ L.ro ++ [L.ARGS], w.Disjoint r
  wrw : L.rw.Pairwise Region.Disjoint
  fits : ∀ r ∈ L.ro ++ L.rw, r.base.toNat + r.len ≤ 2 ^ 32
  args : ∀ j < L.argv.length, σ.mem.readW (L.argA j) 32 = L.argv.getD j 0

structure St (σ s : State) : Prop where
  ok : L.Ok σ
  sp : s.gpr .esp = L.B
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame L.W σ.mem s.mem

end Lay

namespace Lay

variable {L : Lay}

theorem fr_toNat (h : L.B.toNat + L.F + 20 + L.A ≤ 2 ^ 32) {d : Nat} (hd : d < L.F + 20 + L.A) :
    (L.fr d).toNat = L.B.toNat + d := by
  simp only [fr, Q]
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := L.B.toNat) (by have := L.B.isLt; omega), Nat.mod_eq_of_lt (a := d) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- `[B + d]` as an address. -/
theorem Ok.addrB {σ : State} (h : L.Ok σ) {d : Nat} (hd : d < L.F + 20 + L.A) :
    addr L.B d = L.fr d :=
  addr_eq (by have := h.fit; omega)

/-- A range of the frames is within our stack. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ L.F + 16) : Region.Sub ⟨L.fr d, n⟩ L.STK := by
  have e : L.fr d = L.Q - BitVec.ofNat 64 L.C + BitVec.ofNat 64 (L.C + d) := by
    simp only [fr]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  exact Offset.sub_base _ (by omega)

theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega)

theorem FR_stk : Region.Sub L.FR L.STK := by
  have := sub_stk (L := L) (d := 0) (n := L.F) (by omega)
  simp only [fr, BitVec.add_zero] at this
  exact this

/-- Two ranges of the frames, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 2 ^ 32)
    (h₂ : d' + n' ≤ 2 ^ 32) : Region.Disjoint ⟨L.fr d, n⟩ ⟨L.fr d', n'⟩ :=
  Offset.disjoint _ hs (by omega) (by omega)

/-- A range of the frames misses the `C` bytes below them. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 2 ^ 32) (hC : L.C ≤ 2 ^ 32) :
    Region.Disjoint ⟨L.fr d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by omega)

theorem Ok.low_eq {σ : State} (h : L.Ok σ) : below L.B L.C = L.LOW := by
  simp only [below, LOW, Q]
  rw [Taint.sub_setWidth h.BC]

/-- An argument's place is in the arguments, apart from what the body writes. -/
theorem Ok.arg_apart {σ : State} (h : L.Ok σ) {j : Nat} (hj : j < L.argv.length) :
    ∀ r ∈ L.W, Region.Disjoint ⟨L.argA j, 4⟩ r := by
  have := h.fit
  simp only [A] at this
  have hBC := h.BC
  have hB := L.B.isLt
  intro r hr
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  have hsub : Region.Sub ⟨L.argA j, 4⟩ L.ARGS := by
    simp only [argA, Impl.RsaPkcs1Sig.X86.argOff, ARGS, A]
    exact Offset.sub _ (by omega) (by omega)
  rcases hr with rfl | hr | rfl
  · exact Offset.disjoint_base _ (by simp only [Impl.RsaPkcs1Sig.X86.argOff]; omega)
      (by simp only [Impl.RsaPkcs1Sig.X86.argOff]; omega)
  · exact ((h.wro r hr L.ARGS (List.mem_append_right _ (List.mem_singleton_self _))).sub_right hsub).symm
  · exact fr_low (by simp only [Impl.RsaPkcs1Sig.X86.argOff]; omega) (by omega)

/-- An argument's place may be read. -/
theorem Ok.arg_read {σ : State} (h : L.Ok σ) {j : Nat} (hj : j < L.argv.length) :
    InRegions (σ.rd ++ σ.wr) (L.argA j) 4 := by
  have := h.fit
  simp only [A] at this
  refine ⟨L.ARGS, List.mem_append_right _ (by rw [h.wr]; simp), ?_⟩
  simp only [argA, Impl.RsaPkcs1Sig.X86.argOff, ARGS, A]
  exact Offset.contains _ (by omega) (by omega) (by omega)

namespace Ok

variable {σ : State} (h : L.Ok σ)
include h

theorem stk_fr {R : Region} (hR : R ∈ L.ro ∨ R ∈ L.rw) {d n : Nat} (hd : d + n ≤ L.F + 16) :
    Region.Disjoint ⟨L.fr d, n⟩ R :=
  ((h.stk R (List.mem_append.mpr hR)).sub_left (sub_stk hd))

theorem low_buf {R : Region} (hR : R ∈ L.ro ∨ R ∈ L.rw) : L.LOW.Disjoint R :=
  (h.stk R (List.mem_append.mpr hR)).sub_left low_stk

theorem rw_ro {w r : Region} (hw : w ∈ L.rw) (hr : r ∈ L.ro) : w.Disjoint r :=
  h.wro w hw r (List.mem_append_left _ hr)

/-- The push misses what the body writes. -/
theorem save_apart : ∀ r ∈ L.W, L.SAVE.Disjoint r := by
  have := h.fit
  have := h.BC
  have := L.B.isLt
  intro r hr
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · exact (h.stk r (List.mem_append_right _ hr)).sub_left (sub_stk (by omega))
  · exact fr_low (by omega) (by omega)

/-- So does the return address. -/
theorem ret_apart : ∀ r ∈ L.W, L.RET.Disjoint r := by
  have := h.fit
  have := h.BC
  have := L.B.isLt
  intro r hr
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact h.ret r hr
  · exact fr_low (by omega) (by omega)

end Ok

namespace St

variable {σ s t : State}

theorem arg (h : L.St σ s) {j : Nat} (hj : j < L.argv.length) :
    s.mem.readW (L.argA j) 32 = L.argv.getD j 0 := by
  rw [h.frame.readW (r := ⟨L.argA j, 4⟩) (Region.contains_self _ _) (h.ok.arg_apart hj) (by decide)]
  exact h.ok.args j hj

/-- A buffer only read keeps its bytes. -/
theorem ro {R : Region} (h : L.St σ s) (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt s.mem R.base R.len = Spec.Rsa.bytesAt σ.mem R.base R.len := by
  refine bytesAt_frame h.frame (fun r hr => ?_) (by have := h.ok.fits R (List.mem_append_left _ hR); omega)
  simp only [W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left FR_stk).symm
  · exact (h.ok.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left low_stk).symm

/-- A call stores its return address in `LOW`. -/
theorem callEntry_frame (h : L.St σ s) (hC : 4 ≤ L.C) : Frame [L.LOW] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp, ← h.ok.low_eq]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (k := 4) hC h.ok.BC (by decide))

/-- A buffer only read keeps its bytes in a callee's entry state. -/
theorem callEntry_ro {R : Region} (h : L.St σ s) (hC : 4 ≤ L.C) (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt s.callEntry.mem R.base R.len = Spec.Rsa.bytesAt σ.mem R.base R.len := by
  refine (bytesAt_frame (h.callEntry_frame hC) (fun r hr => ?_)
    (by have := h.ok.fits R (List.mem_append_left _ hR); omega)).trans (h.ro hR)
  simp only [List.mem_singleton] at hr; subst hr
  exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left low_stk).symm

/-- The same state, but for registers and flags. -/
theorem regs (h : L.St σ s) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp)
    (m : t.mem = s.mem) : L.St σ t :=
  ⟨h.ok, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, m ▸ h.frame⟩

theorem upd (h : L.St σ s) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) : L.St σ t :=
  h.regs u.rd u.wr (u.other _ (Ne.symm hd)) u.mem

theorem fupd (h : L.St σ s) (u : Fupd s t) : L.St σ t :=
  h.regs u.rd u.wr (by rw [u.gpr]) u.mem

/-- Memory changed within the frame or the writable buffers. -/
theorem write (h : L.St σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ R ∈ L.W, Region.Sub r R) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .esp = s.gpr .esp) : L.St σ t :=
  ⟨h.ok, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans (hf.sub hs)⟩

/-- A store into the frame. -/
theorem frameW (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) (hf : Frame [⟨L.fr d, n⟩] s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) : L.St σ t :=
  h.write hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.FR, List.mem_cons_self .., Offset.sub_base _ hd⟩) rd wr sp

/-- A range of the frame may be written. -/
theorem inFr (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) : InRegions s.wr (L.fr d) n :=
  ⟨L.FR, by rw [h.wr, h.ok.wr]; simp, Offset.contains_base _ hd (by have := h.ok.fit; omega)⟩

theorem inFrR (h : L.St σ s) {d n : Nat} (hd : d + n ≤ L.F) : InRegions (s.rd ++ s.wr) (L.fr d) n :=
  let ⟨r, hr, hc⟩ := h.inFr hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A buffer we write may be written. -/
theorem inRw (h : L.St σ s) {R : Region} (hR : R ∈ L.rw) : R ∈ s.wr := by
  rw [h.wr, h.ok.wr]; simp [hR]

/-- A buffer we read may be read. -/
theorem inRo (h : L.St σ s) {R : Region} (hR : R ∈ L.ro) : R ∈ s.rd ++ s.wr := by
  rw [h.rd, h.ok.rd]; exact List.mem_append_left _ hR

/-- `mov r, [esp + off]` of argument `j`. -/
theorem wp_arg (h : L.St σ s) {j : Nat} (hj : j < L.argv.length) {r : Reg} (hr : r ≠ .esp)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, L.St σ t → Upd s t r (L.argv.getD j 0) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.esp, Impl.RsaPkcs1Sig.X86.argOff L.F j⟩) :: is)) s Q := by
  have ha : addr L.B (Impl.RsaPkcs1Sig.X86.argOff L.F j) = L.argA j :=
    h.ok.addrB (by simp only [Impl.RsaPkcs1Sig.X86.argOff, A]; omega)
  refine wp_ldm (B := L.B) h.sp (by rw [ha, h.rd, h.wr]; exact h.ok.arg_read hj) fun t u => ?_
  rw [ha, h.arg hj] at u
  exact k t (h.upd u hr) u

/-- Argument `j`, as an operand. -/
theorem readArg (h : L.St σ s) {j : Nat} (hj : j < L.argv.length) :
    readSrc s (.mem ⟨.esp, Impl.RsaPkcs1Sig.X86.argOff L.F j⟩) = some (L.argv.getD j 0) := by
  have ha : addr L.B (Impl.RsaPkcs1Sig.X86.argOff L.F j) = L.argA j :=
    h.ok.addrB (by simp only [Impl.RsaPkcs1Sig.X86.argOff, A]; omega)
  rw [readSrc_mem h.sp (by rw [ha, h.rd, h.wr]; exact h.ok.arg_read hj), ha, h.arg hj]

/-- A word of the frame, as an operand. -/
theorem readSlot (h : L.St σ s) {d : Nat} (hd : d + 4 ≤ L.F) :
    readSrc s (.mem ⟨.esp, d⟩) = some (s.mem.readW (L.fr d) 32) := by
  have ha : addr L.B d = L.fr d := h.ok.addrB (by omega)
  rw [readSrc_mem h.sp (by rw [ha]; exact h.inFrR hd), ha]

/-- `mov r, [esp + d]` of a word of the frame. -/
theorem wp_slot (h : L.St σ s) {d : Nat} (hd : d + 4 ≤ L.F) {r : Reg} (hr : r ≠ .esp) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, L.St σ t → Upd s t r (s.mem.readW (L.fr d) 32) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.esp, d⟩) :: is)) s Q := by
  have ha : addr L.B d = L.fr d := h.ok.addrB (by omega)
  refine wp_ldm (B := L.B) h.sp (by rw [ha]; exact h.inFrR hd) fun t u => ?_
  rw [ha] at u
  exact k t (h.upd u hr) u

/-- `mov [esp + d], r` into the frame. -/
theorem wp_strFr (h : L.St σ s) {d : Nat} (hd : d + 4 ≤ L.F) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, L.St σ t → Mupd s t (s.mem.writeW (L.fr d) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.esp, d⟩ r :: is)) s Q := by
  have ha : addr L.B d = L.fr d := h.ok.addrB (by omega)
  refine wp_stm (B := L.B) h.sp (by rw [ha]; exact h.inFr hd) fun t u => k t ?_ (by rw [← ha]; exact u)
  refine h.frameW hd ?_ u.rd u.wr (by rw [u.gpr])
  rw [u.mem, ha]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end St

/-- A word of the frame read after another is written. -/
theorem readW_fr_other (L : Lay) (m : Mem) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 32) (he : e + 4 ≤ 2 ^ 32) :
    (m.writeW (L.fr e) v).readW (L.fr d) 32 = m.readW (L.fr d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

end Lay

end VG.Proof.RsaPkcs1Sig.X86
