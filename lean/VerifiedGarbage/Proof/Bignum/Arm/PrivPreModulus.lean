module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPrePhase
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreEnter
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.PrepareModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-! # The modulus' values, and `pre` masked by the acceptance bit

`pre` holds the modulus' values, then p's, then q's. Once both factors' are
written, the main workspace gives `R² mod n` (for a modulus replaced by 3
when the key is rejected, whose values the mask then clears), the public
precomputation's export writes `n` and it, and the acceptance bit masks all
of `pre`.
-/

@[expose] public section


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_mov wp_dp op2_reg op2_imm op2_lsl op2_lsr dpVal)

/-! ## Words of `pre` -/

theorem wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) = Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (Mont.off p (8 * a)) b := by
  simp only [Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg (_ ++ ·) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem wordsAt_of_bytes {m m' : Mem} {p : Addr} {n : Nat}
    (h : Spec.Rsa.bytesAt m' p (8 * n) = Spec.Rsa.bytesAt m p (8 * n)) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine Mem.readW_congr fun k hk => ?_
  have e := congrArg (fun l : List Byte => l[8 * i + k]?) h
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega : 8 * i + k < 8 * n),
    Option.map_some, Option.some.injEq] at e
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact e

theorem wordsAt_of_zero_bytes {m : Mem} {p : Addr} {n : Nat}
    (h : Spec.Rsa.bytesAt m p (8 * n) = List.replicate (8 * n) 0) :
    Spec.Rsa.wordsAt m p n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range, List.length_replicate]
  · intro i hi _
    have hi' : i < n := by simpa only [Spec.Rsa.wordsAt, List.length_map, List.length_range] using hi
    simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    have hz : m.read (p + BitVec.ofNat 64 (8 * i)) (64 / 8) = 0 := by
      refine Mem.read_eq_of_bytes fun k hk => ?_
      have hk : k < 8 := hk
      have e := congrArg (fun l : List Byte => l[8 * i + k]?) h
      simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega : 8 * i + k < 8 * n),
        Option.map_some, List.getElem?_replicate, show 8 * i + k < 8 * n by omega, ite_true,
        Option.some.injEq] at e
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, e]
      simp
    rw [Mem.readW, hz]
    rfl

/-! ## The addresses -/

/-- The modulus' values end at `pre + 16 w`. -/
def ppDestP (g : CrtGeometry) : BitVec 32 := g.output + BitVec.ofNat 32 (16 * g.words)
/-- p's values end at `pre + 16 w + 8 w_p`. -/
def ppDestQ (g : CrtGeometry) : BitVec 32 :=
  g.output + BitVec.ofNat 32 (16 * g.words + 8 * ppWords g.pLength)

theorem shl_ofNat (x k : Nat) : BitVec.ofNat 32 x <<< k = BitVec.ofNat 32 (2 ^ k * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mul_comm]

theorem pp_modulusEnd_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa (.block modulusEnd) s fun t =>
      t.gpr .r4 = ppDestP g ∧ t.mem = s.mem ∧ Rest [.r1, .r4] s t := by
  have main := h.buffers.context.main
  unfold modulusEnd
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide)
    (addr_add (by have := h.stack.nowrap; omega)) (h.stack.read (by decide)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (by rw [a.sp]; exact addr_add (by have := h.stack.nowrap; omega))
    (by rw [a.rd, a.wr]; exact h.stack.read (by decide)) fun v b => ?_
  have base : v.gpr .r1 = g.base := by rw [b.gpr, a.mem]; exact h.savedMain
  refine wp_ldr (a := off (State.addr g.base) 48) (by decide)
    (by rw [base]; exact addr_add (by have := main.nowrap; have := h.main.toCrtLayoutState.size; omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact main.read (by have := h.main.toCrtLayoutState.size; omega)) fun z c => ?_
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun t d => WP.block_nil ?_
  refine ⟨?_, d.mem.trans (c.mem.trans (b.mem.trans a.mem)),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans (d.rest (by decide))))⟩
  rw [d.gpr, dpVal, c.other .r4 (by decide), c.gpr, b.other .r4 (by decide), a.gpr, b.mem, a.mem,
    h.main.toCrtLayoutState.nativeCount main, h.stack.output, ppDestP, shl_ofNat]

theorem pp_pDest_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa (.block pDest) s fun t =>
      t.gpr .r4 = ppDestP g ∧ t.gpr .r2 = BitVec.ofNat 32 4 ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r7] s t := by
  rw [pDest, WP.block_append_iff]
  refine WP.mono (pp_modulusEnd_ok s h) ?_
  rintro u ⟨dst, mem, rest⟩
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  exact ⟨(a.other .r4 (by decide)).trans dst, a.gpr, a.mem.trans mem,
    (rest.mono (by decide)).trans (a.rest (by decide))⟩

theorem pp_qDest_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa (.block qDest) s fun t =>
      t.gpr .r4 = ppDestQ g ∧ t.gpr .r2 = BitVec.ofNat 32 4 ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r7] s t := by
  obtain ⟨_, le, _, pos, _, _⟩ := h.pp_fits 1 (Or.inl rfl)
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  rw [qDest, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pp_modulusEnd_ok s h) ?_
  rintro u ⟨dst, mem, rest⟩
  have shared := h.of_mem mem rest
  refine WP.mono (primeWidth_ok u (slot := 68) (by decide) (by have := shared.stack.nowrap; omega)
    (shared.stack.read (by decide)) (shared.stack.length 1) pos (by have := h.buffers.lengthValid.2; omega)) ?_
  rintro v ⟨width, _, memV, restV⟩
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun z a => ?_
  refine wp_mov (op2_imm (by decide)) fun t b => WP.block_nil ?_
  refine ⟨?_, b.gpr, b.mem.trans (a.mem.trans (memV.trans mem)),
    (rest.mono (by decide)).trans ((restV.mono (by decide)).trans ((a.rest (by decide)).trans (b.rest (by decide))))⟩
  have r4 : v.gpr .r4 = ppDestP g := (restV.gpr .r4 (by decide)).trans dst
  rw [b.other .r4 (by decide), a.gpr, dpVal]
  rw [r4, width]
  change ppDestP g + BitVec.ofNat 32 (ppWords g.pLength) <<< 3 = _
  rw [ppDestP, ppDestQ, shl_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `pre`'s words: the modulus', then each factor's. -/
def ppPreWords (g : CrtGeometry) : Nat := 2 * g.words + ppWords g.pLength + ppWords g.qLength

theorem pp_maskArgs_ok (s : State) {g : CrtGeometry} (stack : CrtCallStack g s)
    (saved : s.mem.readW (off (State.addr s.sp) 8) 32 = g.base)
    (mainFit : g.base.toNat + 52 ≤ 2 ^ 32) (mainRead : InRegions (s.rd ++ s.wr) (off (State.addr g.base) 48) 4)
    (count : s.mem.readW (off (State.addr g.base) 48) 32 = BitVec.ofNat 32 g.words)
    (valid : Spec.Rsa.lenValid g.length) (pPositive : 0 < g.pLength) (pShort : g.pLength < g.length)
    (qPositive : 0 < g.qLength) (qShort : g.qLength < g.length) :
    WP isa (.block maskArgs) s fun t =>
      t.gpr .r4 = g.output ∧ t.gpr .r6 = BitVec.ofNat 32 (8 * ppPreWords g) ∧ t.mem = s.mem ∧
      Rest [.r1, .r3, .r4, .r6, .r7] s t := by
  have hl := valid.2
  unfold maskArgs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := stack.nowrap; omega)) (stack.read (by decide)) fun u a => ?_
  refine wp_ldr (a := off (State.addr g.base) 48) (by decide)
    (by rw [a.gpr, saved]; exact addr_add (by omega)) (by rw [a.rd, a.wr]; exact mainRead) fun v b => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun z c => WP.block_nil ?_
  have stackZ : CrtCallStack g z := by
    have f : Frame [] s.mem z.mem := by rw [c.mem, b.mem, a.mem]; exact Frame.refl _ _
    have r : Rest [.r1, .r6] s z := (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))
    exact stack.after_outside f r (by simp)
  have r6z : z.gpr .r6 = BitVec.ofNat 32 (16 * g.words) := by
    rw [c.gpr, b.gpr, a.mem, count, shl_ofNat]
  refine WP.mono (primeWidth_ok z (slot := 68) (by decide) (by have := stackZ.nowrap; omega)
    (stackZ.read (by decide)) (stackZ.length 1) pPositive (by change g.pLength < _; omega)) ?_
  rintro y ⟨wp, _, memY, restY⟩
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun x d => WP.block_nil ?_
  have stackX : CrtCallStack g x := by
    have f : Frame [] z.mem x.mem := by rw [d.mem, memY]; exact Frame.refl _ _
    have r : Rest [.r1, .r3, .r6, .r7] z x := (restY.mono (by decide)).trans (d.rest (by decide))
    exact stackZ.after_outside f r (by simp)
  have r6x : x.gpr .r6 = BitVec.ofNat 32 (16 * g.words + 8 * ppWords g.pLength) := by
    rw [d.gpr, dpVal, restY.gpr .r6 (by decide), r6z, wp]
    change _ + BitVec.ofNat 32 (ppWords g.pLength) <<< 3 = _
    rw [shl_ofNat, ← BitVec.ofNat_add]
  refine WP.mono (primeWidth_ok x (slot := 76) (by decide) (by have := stackX.nowrap; omega)
    (stackX.read (by decide)) (stackX.length 2) qPositive (by change g.qLength < _; omega)) ?_
  rintro e ⟨wq, _, memE, restE⟩
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun f i => ?_
  refine wp_loadStack (a := off (State.addr f.sp) 4) (by decide)
    (addr_add (by rw [i.sp, restE.sp, d.sp, restY.sp, c.sp, b.sp, a.sp]; have := stack.nowrap; omega))
    (by rw [i.rd, i.wr, i.sp, restE.rd, restE.wr, restE.sp]; exact stackX.read (by decide)) fun t j => WP.block_nil ?_
  have memT : t.mem = s.mem := by rw [j.mem, i.mem, memE, d.mem, memY, c.mem, b.mem, a.mem]
  refine ⟨?_, ?_, memT, ?_⟩
  · rw [j.gpr, i.mem, memE, i.sp, restE.sp]; exact stackX.output
  · rw [j.other .r6 (by decide), i.gpr, dpVal, restE.gpr .r6 (by decide), r6x, wq]
    change _ + BitVec.ofNat 32 (ppWords g.qLength) <<< 3 = _
    rw [shl_ofNat, ← BitVec.ofNat_add, ppPreWords]
    congr 1
    omega
  · exact (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((restY.mono (by decide)).trans ((d.rest (by decide)).trans ((restE.mono (by decide)).trans
        ((i.rest (by decide)).trans (j.rest (by decide))))))))

end VG.Proof.Bignum.Arm


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

/-- `pre`: writable, apart from the CRT's storage, frame and sources but
the input and the coefficient, which are its first bytes. -/
structure PpPre (g : CrtGeometry) (s : State) : Prop where
  fit : g.output.toNat + 8 * ppPreWords g ≤ 2 ^ 32
  write : InRegions s.wr (State.addr g.output) (8 * ppPreWords g)
  workspace : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  stack : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  sources : ∀ i : Fin 7, i ≠ 1 → i ≠ 6 →
    Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩
  input : g.input = g.output
  qi : g.qi = g.output

theorem PpPre.after {g : CrtGeometry} {s t : State} {rs : List Reg} (h : PpPre g s) (rest : Rest rs s t) :
    PpPre g t :=
  ⟨h.fit, by rw [rest.wr]; exact h.write, h.workspace, by rw [rest.sp]; exact h.stack, h.sources, h.input, h.qi⟩

theorem PpPre.words_le {g : CrtGeometry} {s : State} (_h : PpPre g s) :
    2 ≤ ppWords g.pLength ∧ 2 ≤ ppWords g.qLength := by
  simp only [ppWords]; omega

theorem PpPre.addrP {g : CrtGeometry} {s : State} (h : PpPre g s) :
    State.addr (ppDestP g) = Mont.off (State.addr g.output) (16 * g.words) := by
  have := h.fit
  have := h.words_le
  simp only [ppPreWords] at *
  exact addr_add (by omega)

theorem PpPre.addrQ {g : CrtGeometry} {s : State} (h : PpPre g s) :
    State.addr (ppDestQ g) = Mont.off (State.addr g.output) (16 * g.words + 8 * ppWords g.pLength) := by
  have := h.fit
  have := h.words_le
  simp only [ppPreWords] at *
  exact addr_add (by omega)

/-- A segment of `pre` from `16 w` bytes on: apart from everything the CRT keeps. -/
theorem PpPre.dest {g : CrtGeometry} {s : State} (h : PpPre g s) (lengthLe : g.length ≤ 8 * g.words)
    (pLe : g.pLength ≤ 8 * g.words) {d : BitVec 32} {o n : Nat}
    (addr : State.addr d = Mont.off (State.addr g.output) o) (low : 16 * g.words ≤ o) (high : o + n ≤ 8 * ppPreWords g) :
    PpDest g d n s := by
  have fit := h.fit
  have sub : Region.Sub ⟨State.addr d, n⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ := by
    rw [addr]; exact Offset.sub_base _ high
  have below (k : Nat) (hk : k ≤ 8 * g.words) :
      Region.Disjoint ⟨State.addr g.output, k⟩ ⟨State.addr d, n⟩ := by
    rw [addr]; exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  refine ⟨?_, ?_, h.workspace.sub_right sub, h.stack.sub_right sub, ?_⟩
  · have e : d.toNat = g.output.toNat + o := by
      have := congrArg BitVec.toNat addr
      simp only [State.addr, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
      omega
    omega
  · rw [addr]; exact CallLay.inRegions_sub h.write high (by omega)
  · intro i
    by_cases h1 : i = 1
    · subst h1
      change Region.Disjoint ⟨State.addr g.input, g.length⟩ _
      rw [h.input]; exact below _ lengthLe
    by_cases h6 : i = 6
    · subst h6
      change Region.Disjoint ⟨State.addr g.qi, g.pLength⟩ _
      rw [h.qi]; exact below _ pLe
    exact (h.sources i h1 h6).sub_right sub

theorem flag_bool (b : Prop) [Decidable b] :
    (if b then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide b).toNat := by
  by_cases hb : b <;> simp [hb]

/-- p's workspace selected, through the main one. -/
theorem pp_selectP_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa selectP s fun t => CrtShared g bs t ∧
      LayoutFrameReady (crtP g.base g.words) (workspaceWords g.words) g.words t ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  rw [selectP, WP.seq_iff]
  refine WP.mono (crt_selectMain_ready s h) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  refine WP.mono (crt_selectLinked_ready u sharedU sharedU.buffers.context.p sharedU.p (by simp [crtRegions])
    (by have := sharedU.buffers.context.size; omega : 224 + 4 ≤ 8 * workspaceWords g.words) (by decide)
    readyU.ptr sharedU.main.p) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  rw [restU.sp] at frameT
  exact ⟨sharedT, readyT, frameU.trans frameT, restU.trans restT⟩

/-- `n` copied into p's workspace and `R² mod n` computed there, where the
factors' preparations fold it and the end exports both. -/
theorem pp_modulusR2_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa modulusR2 s fun t => CrtShared g bs t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0) ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 4 = 2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0) ∧
      Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  rw [modulusR2, WP.seq_iff]
  refine WP.mono (pp_selectP_ok s h) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  rw [WP.seq_iff]
  refine wp_loadStack (a := off (State.addr u.sp) 8) (by decide)
    (addr_add (by have := sharedU.stack.nowrap; omega)) (sharedU.stack.read (by decide)) fun x a => WP.block_nil ?_
  have ra : Rest [.r1] u x := a.rest (by decide)
  have r1 : x.gpr .r1 = g.base := a.gpr.trans sharedU.savedMain
  have readyX := readyU.of_mem a.mem ra ((a.other .r0 (by decide)).trans readyU.ptr)
  rw [WP.seq_iff]
  refine WP.mono (transferArray_ok x (o := 0) (a := 0) ⟨readyX, sharedU.buffers.context.main.congr ra.wr,
    by rw [a.mem]; exact sharedU.main.toCrtLayoutState, r1, sharedU.buffers.context.sepMP⟩ (by decide) (by decide)) ?_
  rintro y ⟨readyY, numY, _, frameY, restY⟩
  rw [a.mem, sharedU.modulus] at numY
  rw [a.mem] at frameY
  obtain ⟨odd, gt, _⟩ := valid_facts sharedU.valid h.buffers.lengthValid.1
  have pm : PrecomputeModulus (crtP g.base g.words) (workspaceWords g.words) g.words y :=
    ⟨⟨readyY.workspace, readyY.layout, readyY.width, readyY.ptr, readyY.stackRead, readyY.stackSep, readyY.saved⟩,
      by rw [numY]; exact gt, by rw [numY]; exact odd⟩
  refine WP.mono (prepareModulus_ok y pm (by omega)) ?_
  rintro t ⟨dl, modT, r2T, frameT, restT⟩
  rw [numY] at modT r2T
  have restUT : Rest roundClobbers u t := (ra.mono (by decide)).trans (restY.trans restT)
  have frameUT : Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩] u.mem t.mem :=
    frameY.trans frameT
  have sharedT := sharedU.after_p (frameUT.mono (by simp)) restUT ⟨dl.layout, dl.width⟩
  refine ⟨sharedT, modT, r2T, (frameU.mono (by simp)).trans (frameUT.mono (by simp)),
    (restU.mono (by decide)).trans restUT⟩

theorem pp_modulusPart_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (pre : PpPre g s)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0))
    (pn : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0))
    (pr2 : numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 = 2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0))
    {X Y : List (BitVec 64)}
    (segP : Spec.Rsa.wordsAt s.mem (State.addr (ppDestP g)) (ppWords g.pLength) = X)
    (segQ : Spec.Rsa.wordsAt s.mem (State.addr (ppDestQ g)) (ppWords g.qLength) = Y) :
    WP isa modulusPart s fun t =>
      t.gpr .r0 = (if crtAccepted bs then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) =
        (if crtAccepted bs then
          Spec.Rsa.toWords (Spec.Rsa.os2ip (bs 0)) g.words ++
            Spec.Rsa.toWords (2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0)) g.words ++ X ++ Y
        else List.replicate (ppPreWords g) 0) ∧
      Frame [⟨State.addr g.base, g.size⟩, ⟨State.addr s.sp, 4⟩, ⟨State.addr g.output, 8 * ppPreWords g⟩]
        s.mem t.mem ∧
      Rest roundClobbers s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  have lengthValid := h.buffers.lengthValid
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have wordsTwo : 8 ≤ g.words := by
    change 8 ≤ Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; have := lengthValid.1; omega
  have preFit := pre.fit
  have twoP := pre.words_le
  have mainWs := h.buffers.context.main
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  have mainSize : 256 ≤ 8 * workspaceWords g.words := h.main.toCrtLayoutState.size
  have bitFlag : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1 := by
    rw [flag]; split <;> decide
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  -- p's workspace selected.
  rw [modulusPart, WP.seq_iff]
  refine WP.mono (pp_selectP_ok s h) ?_
  rintro v ⟨sharedV, dl, frameV, restV⟩
  have stackV : CrtCallStack g v := sharedV.stack
  have pV : numAt v.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0) :=
    (h.p_num (regions := []) frameV (by simp) (by decide)).trans pn
  have pR2V : numAt v.mem (State.addr (crtP g.base g.words)) g.words 4 = 2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0) :=
    (h.p_num (regions := []) frameV (by simp) (by decide)).trans pr2
  -- `pre` in r4.
  rw [WP.seq_iff]
  refine wp_loadStack (a := off (State.addr v.sp) 4) (by decide)
    (addr_add (by have := stackV.nowrap; omega)) (stackV.read (by decide)) fun x a => WP.block_nil ?_
  have r4X : x.gpr .r4 = g.output := a.gpr.trans stackV.output
  have restVX : Rest roundClobbers s x := (restV.mono (by decide)).trans (a.rest (by decide))
  -- `n` and `R² mod n` exported.
  have sixteen : (⟨State.addr g.output, 16 * g.words⟩ : Region).Sub ⟨State.addr g.output, 8 * ppPreWords g⟩ :=
    Region.sub_prefix (by simp only [ppPreWords]; omega)
  have preWs : Region.Disjoint ⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩
      ⟨State.addr g.output, 16 * g.words⟩ :=
    (pre.workspace.sub_left pSub).sub_right sixteen
  have preMain : Region.Disjoint ⟨State.addr g.base, 8 * workspaceWords g.words⟩ ⟨State.addr g.output, 16 * g.words⟩ :=
    (pre.workspace.sub_left mainSub).sub_right sixteen
  have write16 : InRegions x.wr (State.addr g.output) (16 * g.words) := by
    rw [restVX.wr]
    have := CallLay.inRegions_sub (off := 0) (l := 16 * g.words) pre.write
      (by simp only [ppPreWords]; omega) (by omega)
    simpa only [BitVec.add_zero] using this
  have fit16 : g.output.toNat + 16 * g.words ≤ 2 ^ 32 := by simp only [ppPreWords] at preFit; omega
  rw [WP.seq_iff]
  refine WP.mono (precomputeOut_ok x (w := g.words) (dst := g.output) (dl.workspace.congr a.wr)
    (by rw [a.mem]; exact dl.layout) (by rw [a.mem]; exact dl.width) fit16 write16
    preWs ((a.other .r0 (by decide)).trans dl.ptr) r4X) ?_
  rintro y ⟨_, wordsY, frameY, restY⟩
  rw [a.mem, pV, pR2V] at wordsY
  rw [a.mem] at frameY
  have mainEqY : WorkspaceEq (State.addr g.base) (8 * workspaceWords g.words) v.mem y.mem :=
    WorkspaceEq.of_frame (by have := mainWs.nowrap; omega) frameY
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact preMain)
  have layoutY := mainEqY.layout sharedV.main.layout
  have widthY := (mainEqY.width (by omega)).trans sharedV.main.width
  have stackSepOut : ∀ r ∈ [(⟨State.addr g.output, 16 * g.words⟩ : Region)],
      (⟨State.addr x.sp, 112⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [restVX.sp]; exact pre.stack.sub_right sixteen
  have ra : Rest [.r4] v x := a.rest (by decide)
  have stackX : CrtCallStack g x :=
    stackV.after_outside (regions := []) (by rw [a.mem]; exact Frame.refl _ _) ra (by simp)
  have stackY : CrtCallStack g y := stackX.after_outside (by rw [a.mem]; exact frameY) restY stackSepOut
  have restAllY : Rest roundClobbers s y := restVX.trans restY
  -- Everything so far wrote the frame's slot 0 and `pre`'s first `16 w` bytes.
  let L : List Region := [⟨State.addr s.sp, 4⟩, ⟨State.addr g.output, 16 * g.words⟩]
  have frameSY : Frame L s.mem y.mem := by
    have f1 : Frame L s.mem v.mem := frameV.mono (by simp [L])
    have f3 : Frame L v.mem y.mem := frameY.mono (by simp [L])
    exact f1.trans f3
  have keptY {d : Nat} (low : 4 ≤ d) (fit : d + 4 ≤ 112) :
      y.mem.readW (off (State.addr y.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
    rw [restAllY.sp]
    have sub : Region.Sub ⟨off (State.addr s.sp) d, 4⟩ ⟨State.addr s.sp, 112⟩ := Offset.sub_base _ fit
    refine frameSY.readW (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ low (by omega)
    · exact (pre.stack.sub_right sixteen).sub_left sub
  have flagY : y.mem.readW (off (State.addr y.sp) 48) 32 = BitVec.ofNat 32 (decide (crtAccepted bs)).toNat := by
    rw [keptY (d := 48) (by decide) (by decide), flag, flag_bool]
  have countY : y.mem.readW (off (State.addr g.base) 48) 32 = BitVec.ofNat 32 g.words := by
    have header := nativeHeader_of_layout y.mem g.base mainWs.nowrap (Nat.le_refl _) layoutY
    rw [widthY] at header
    exact header.count
  have mainWsY := mainWs.congr restAllY.wr
  -- The length of `pre`, and the mask.
  obtain ⟨_, leP, _, _, _, _⟩ := h.pp_fits 1 (Or.inl rfl)
  obtain ⟨_, leQ, _, _, _, _⟩ := h.pp_fits 2 (Or.inr rfl)
  change ppWords g.pLength ≤ g.words at leP
  change ppWords g.qLength ≤ g.words at leQ
  rw [WP.seq_iff]
  refine WP.mono (pp_maskArgs_ok y stackY (by rw [keptY (d := 8) (by decide) (by decide)]; exact h.savedMain)
    (by have := mainWs.nowrap; omega) (mainWsY.read (by omega)) countY lengthValid h.buffers.pPositive
    h.buffers.pShort h.buffers.qPositive h.buffers.qShort) ?_
  rintro z ⟨r4Z, r6Z, memZ, restZ⟩
  have restAllZ : Rest roundClobbers s z := restAllY.trans (restZ.mono (by decide))
  have stackZ : CrtCallStack g z := stackY.after_outside (regions := []) (by rw [memZ]; exact Frame.refl _ _) restZ (by simp)
  have preZ := pre.after restAllZ
  refine WP.mono (maskOutput_ok z (k := 8 * ppPreWords g) (accepted := decide (crtAccepted bs))
    (by simp only [ppPreWords]; omega) (by simp only [ppPreWords]; omega) preFit preZ.write
    (by have := stackZ.nowrap; omega) (stackZ.read (by decide))
    (by rw [memZ, restZ.sp]; exact flagY) r4Z r6Z) ?_
  rintro t ⟨bytes, r0T, frameT, restT⟩
  have restAll : Rest roundClobbers s t := restAllZ.trans (restT.mono (by decide))
  have destP : PpDest g (ppDestP g) (8 * ppWords g.pLength) s :=
    pre.dest wordsLen (by have := h.buffers.pShort; omega) pre.addrP (Nat.le_refl _)
      (by simp only [ppPreWords]; omega)
  have destQ : PpDest g (ppDestQ g) (8 * ppWords g.qLength) s :=
    pre.dest wordsLen (by have := h.buffers.pShort; omega) pre.addrQ (by omega)
      (by simp only [ppPreWords]; omega)
  have keepSeg {d : BitVec 32} {n o : Nat} (dest : PpDest g d (8 * n) s)
      (addr : State.addr d = Mont.off (State.addr g.output) o) (low : 16 * g.words ≤ o)
      (high : o + 8 * n ≤ 2 ^ 32) :
      Spec.Rsa.wordsAt y.mem (State.addr d) n = Spec.Rsa.wordsAt s.mem (State.addr d) n := by
    have fit := dest.fit
    refine Proof.Rsa.wordsAt_frame frameSY (by omega) fun r hr => ?_
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dest.stack.sub_left (Region.sub_prefix (by decide))).symm
    · rw [addr]; exact Offset.disjoint_base _ low (by omega)
  refine ⟨by rw [r0T, flag_bool], ?_, ?_, restAll⟩
  · by_cases acc : crtAccepted bs
    · simp only [acc, decide_true, ite_true] at bytes ⊢
      rw [wordsAt_of_bytes bytes, memZ, ppPreWords, wordsAt_append, wordsAt_append, wordsY,
        show 8 * (2 * g.words) = 16 * g.words by omega, ← pre.addrP,
        show 8 * (2 * g.words + ppWords g.pLength) = 16 * g.words + 8 * ppWords g.pLength by omega,
        ← pre.addrQ, keepSeg destP pre.addrP (Nat.le_refl _) (by simp only [ppPreWords] at preFit; omega),
        keepSeg destQ pre.addrQ (by omega) (by simp only [ppPreWords] at preFit; omega), segP, segQ]
    · simp only [acc, decide_false, Bool.false_eq_true, ite_false] at bytes ⊢
      exact wordsAt_of_zero_bytes bytes
  · have f1 : Frame [⟨State.addr g.base, g.size⟩, ⟨State.addr s.sp, 4⟩, ⟨State.addr g.output, 8 * ppPreWords g⟩]
        s.mem y.mem := by
      refine frameSY.sub fun r hr => ?_
      simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, sixteen⟩
    have f2 : Frame [⟨State.addr g.base, g.size⟩, ⟨State.addr s.sp, 4⟩, ⟨State.addr g.output, 8 * ppPreWords g⟩]
        y.mem t.mem := by rw [← memZ]; exact frameT.mono (by simp)
    exact f1.trans f2

/-- The values the precomputation writes for an accepted key. -/
def ppValues (g : CrtGeometry) (bs : Fin 7 → List Byte) : List (BitVec 64) :=
  Spec.Rsa.toWords (Spec.Rsa.os2ip (bs 0)) g.words ++
    Spec.Rsa.toWords (2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0)) g.words ++
    Spec.Rsa.toWords (2 ^ (128 * ppWords g.pLength) % Spec.Rsa.os2ip (bs 2)) (ppWords g.pLength) ++
    Spec.Rsa.toWords (2 ^ (128 * ppWords g.qLength) % Spec.Rsa.os2ip (bs 3)) (ppWords g.qLength)

/-- The state the CRT's preparation starts from, for a valid modulus. -/
structure PpValidInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  ptr : s.gpr .r0 = g.base
  count : s.gpr .r6 = BitVec.ofNat 32 g.length
  saved : s.mem.readW (State.addr s.sp) 32 = g.base
  modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true

theorem pp_valid_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpValidInput g bs s)
    (pre : PpPre g s) :
    WP isa valid s fun t =>
      t.gpr .r0 = (if crtAccepted bs then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) =
        (if crtAccepted bs then ppValues g bs else List.replicate (ppPreWords g) 0) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, 8 * ppPreWords g⟩]) s.mem t.mem ∧
      Rest roundClobbers s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have preFit := pre.fit
  have twoP := pre.words_le
  have pLe : g.pLength ≤ 8 * g.words := by have := h.buffers.pShort; omega
  have destP : PpDest g (ppDestP g) (8 * ppWords g.pLength) s :=
    pre.dest wordsLen pLe pre.addrP (Nat.le_refl _) (by simp only [ppPreWords]; omega)
  have destQ : PpDest g (ppDestQ g) (8 * ppWords g.qLength) s :=
    pre.dest wordsLen pLe pre.addrQ (by omega) (by simp only [ppPreWords]; omega)
  have sixteenOut (o n : Nat) (lo : 16 * g.words ≤ o) (hi : o + n ≤ 8 * ppPreWords g) :
      (⟨Mont.off (State.addr g.output) o, n⟩ : Region).Sub ⟨State.addr g.output, 8 * ppPreWords g⟩ :=
    Offset.sub_base _ hi
  rw [valid, WP.seq_iff]
  refine WP.mono (crt_begin_ok s h.buffers h.stack h.ptr h.count h.saved h.modulusPtr h.valid) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_validateStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, _, _, _, flagV, frameV, restV⟩
  have restSV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  have bitV : ppFlag v ≤ 1 := by unfold ppFlag; rw [flagV]; split <;> decide
  have accOf {x : State} (hx : ppFlag x = ppFlag v) (ne : ppFlag x ≠ 0) : crtAccepted bs := by
    by_contra acc
    unfold ppFlag at hx ne
    rw [hx, flagV] at ne
    simp [acc] at ne
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  -- `R² mod n`, in p's workspace.
  rw [WP.seq_iff]
  refine WP.mono (pp_modulusR2_ok v sharedV) ?_
  rintro w ⟨sharedW, nW, r2W, frameW, restW⟩
  have flagW : ppFlag w = ppFlag v := by
    unfold ppFlag
    rw [restW.sp]
    refine congrArg BitVec.toNat (frameW.readW (r := ⟨off (State.addr v.sp) 48, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((sharedV.stack.separate.sub_right pSub).sub_left (Offset.sub_base _ (by decide)))
    · exact Offset.disjoint_base _ (by decide) (by decide)
  have restSW : Rest roundClobbers s w := restSV.trans restW
  have sepP := (sharedW.child (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩)).2.2.2.1
  -- p's arrays, kept by a factor's phase.
  have keptP {x y : State} {d : BitVec 32} {n : Nat} (sx : CrtShared g bs x) (dest : PpDest g d n x)
      (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr x.sp, 4⟩,
        ⟨State.addr d, n⟩] x.mem y.mem) {j : Nat} (hj : j < 8) :
      numAt y.mem (State.addr (crtP g.base g.words)) g.words j =
        numAt x.mem (State.addr (crtP g.base g.words)) g.words j := by
    refine sx.p_num (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr d, n⟩])
      (frame.mono (by simp)) (fun r hr => ?_) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sepP
    · exact dest.workspace.sub_left pSub
  -- p's values.
  rw [WP.seq_iff]
  refine WP.mono (pp_phase_ok w sharedW 1 (Or.inl rfl) (dest := pDest) (d := ppDestP g)
    (fun x hx => pp_pDest_ok x hx) (destP.after restSW) (by rw [flagW]; exact bitV)
    (fun ne => (sharedW.accepted_factors (accOf flagW ne)).1)
    (fun ne => ⟨Spec.Rsa.os2ip (bs 3), (accOf flagW ne).2.2.symm⟩) r2W) ?_
  rintro x ⟨sharedX, flagX, segPX, frameX, restX⟩
  have nX := (keptP sharedW (destP.after restSW) frameX (by decide)).trans nW
  have r2X := (keptP sharedW (destP.after restSW) frameX (by decide)).trans r2W
  rw [flagW] at flagX segPX
  have lp : g.sourceLength (Fin.succ 1) = g.pLength := rfl
  have bp : bs (Fin.succ 1) = bs 2 := rfl
  rw [lp, bp] at segPX
  rw [lp] at frameX
  -- q's values.
  have restSX : Rest roundClobbers s x := restSW.trans restX
  rw [WP.seq_iff]
  refine WP.mono (pp_phase_ok x sharedX 2 (Or.inr rfl) (dest := qDest) (d := ppDestQ g)
    (fun y hy => pp_qDest_ok y hy) (destQ.after restSX) (by rw [flagX]; exact bitV)
    (fun ne => (sharedX.accepted_factors (accOf flagX ne)).2)
    (fun ne => ⟨Spec.Rsa.os2ip (bs 2), by rw [Nat.mul_comm]; exact (accOf flagX ne).2.2.symm⟩) r2X) ?_
  rintro y ⟨sharedY, flagY, segQY, frameY, restY⟩
  have nY := (keptP sharedX (destQ.after restSX) frameY (by decide)).trans nX
  have r2Y := (keptP sharedX (destQ.after restSX) frameY (by decide)).trans r2X
  rw [flagX] at flagY segQY
  have lq : g.sourceLength (Fin.succ 2) = g.qLength := rfl
  have bq : bs (Fin.succ 2) = bs 3 := rfl
  rw [lq, bq] at segQY
  rw [lq] at frameY
  have restSY : Rest roundClobbers s y := restSX.trans restY
  have narrowSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits sharedV.narrow_member
  have segPY : Spec.Rsa.wordsAt y.mem (State.addr (ppDestP g)) (ppWords g.pLength) =
      Spec.Rsa.wordsAt x.mem (State.addr (ppDestP g)) (ppWords g.pLength) := by
    have fit := destP.fit
    refine Proof.Rsa.wordsAt_frame frameY (by omega) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (destP.workspace.sub_left narrowSub).symm
    · rw [restSX.sp]; exact (destP.stack.sub_left (Region.sub_prefix (by decide))).symm
    · simp only [ppPreWords] at preFit
      rw [pre.addrP, pre.addrQ]; exact (Offset.disjoint _ (Or.inl (Nat.le_refl _)) (by omega) (by omega))
  have flagYw : y.mem.readW (off (State.addr y.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [← flagV]
    exact BitVec.eq_of_toNat_eq flagY
  refine WP.mono (pp_modulusPart_ok y sharedY (pre.after restSY) flagYw nY r2Y segPY rfl) ?_
  rintro t ⟨r0T, wordsT, frameT, restT⟩
  refine ⟨r0T, ?_, ?_, restSY.trans restT⟩
  · rw [wordsT]
    by_cases acc : crtAccepted bs
    · have ne : ppFlag v ≠ 0 := by unfold ppFlag; rw [flagV]; simp [acc]
      rw [segPX ne, segQY ne]
      simp only [acc, ite_true, ppValues]
    · simp only [acc, ite_false]
  · let T : List Region := crtMutable g s.sp ++ [⟨State.addr g.output, 8 * ppPreWords g⟩]
    have inT (r : Region) (hr : r ∈ crtMutable g s.sp) : ∃ r' ∈ T, r.Sub r' :=
      ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    have wsT : ∃ r' ∈ T, Region.Sub ⟨State.addr g.base, g.size⟩ r' := inT _ (by simp [crtMutable])
    have spT : ∃ r' ∈ T, Region.Sub ⟨State.addr s.sp, 4⟩ r' := inT _ (by simp [crtMutable])
    have preT : ∃ r' ∈ T, Region.Sub ⟨State.addr g.output, 8 * ppPreWords g⟩ r' :=
      ⟨_, List.mem_append_right _ (by simp), fun _ h => h⟩
    have destT {d : BitVec 32} {o n : Nat} (addr : State.addr d = Mont.off (State.addr g.output) o)
        (hi : o + n ≤ 8 * ppPreWords g) : ∃ r' ∈ T, Region.Sub ⟨State.addr d, n⟩ r' := by
      obtain ⟨r', hr', sub⟩ := preT
      exact ⟨r', hr', fun a ha => sub a (by rw [addr] at ha; exact Offset.sub_base _ hi a ha)⟩
    have f1 : Frame T s.mem u.mem := frameU.sub fun r hr => inT r hr
    have f2 : Frame T u.mem v.mem := frameV.sub fun r hr => by
      rw [restU.sp] at hr
      simp only [crtLiveMutable, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact inT _ (by simp [crtMutable])
    have fW : Frame T v.mem w.mem := frameW.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · obtain ⟨r', hr', sub⟩ := wsT; exact ⟨r', hr', fun a ha => sub a (pSub a ha)⟩
      · rw [restSV.sp]; exact spT
    have f3 : Frame T w.mem x.mem := frameX.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨r', hr', sub⟩ := wsT; exact ⟨r', hr', fun a ha => sub a (narrowSub a ha)⟩
      · rw [restSW.sp]; exact spT
      · exact destT pre.addrP (by simp only [ppPreWords]; omega)
    have f4 : Frame T x.mem y.mem := frameY.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨r', hr', sub⟩ := wsT; exact ⟨r', hr', fun a ha => sub a (narrowSub a ha)⟩
      · rw [restSX.sp]; exact spT
      · exact destT pre.addrQ (by simp only [ppPreWords]; omega)
    have f5 : Frame T y.mem t.mem := frameT.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact wsT
      · rw [restSY.sp]; exact spT
      · exact preT
    exact f1.trans (f2.trans (fW.trans (f3.trans (f4.trans f5))))

/-- What the precomputation returns and writes: for a valid modulus whose
factors the CRT's validation accepts, 1 and the values; otherwise 0 and zeros. -/
def ppGood (g : CrtGeometry) (bs : Fin 7 → List Byte) : Prop :=
  Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true ∧ crtAccepted bs

instance (g : CrtGeometry) (bs : Fin 7 → List Byte) : Decidable (ppGood g bs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem pp_body_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s)
    (pre : PpPre g s)
    (cleared : Spec.Rsa.wordsAt s.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) :
    WP isa body s fun t =>
      t.gpr .r0 = (if ppGood g bs then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) =
        (if ppGood g bs then ppValues g bs else List.replicate (ppPreWords g) 0) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, 8 * ppPreWords g⟩]) s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [body, WP.seq_iff]
  refine WP.mono (modulusCheck_ok s h.buffers.lengthValid.1 h.buffers.lengthValid.2
    (h.buffers.source 0).fits (h.buffers.source 0).read h.source h.count) ?_
  rintro u ⟨flag, mem, rest⟩
  have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.buffers.source 0).bytes
  change u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
  rw [nb] at flag
  have hu := h.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ptr)
    ((rest.gpr .r4 (by decide)).trans h.source) ((rest.gpr .r6 (by decide)).trans h.count)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length) (by change some u.z = _; rw [flag]) ?_ ?_
  · intro valid
    refine WP.mono (pp_valid_ok u ⟨hu.buffers, hu.stack, hu.ptr, hu.count, hu.saved, hu.modulusPtr, valid⟩
      (pre.after rest)) ?_
    rintro t ⟨r0, words, frame, restT⟩
    rw [mem, rest.sp] at frame
    refine ⟨?_, ?_, frame, (rest.mono (by decide)).trans restT⟩
    · rw [r0]; simp only [ppGood, valid, true_and]
    · rw [words]; simp only [ppGood, valid, true_and]
  · intro invalid
    refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
    have bad : ¬ ppGood g bs := fun g' => by rw [g'.1] at invalid; exact Bool.false_ne_true invalid.symm
    refine ⟨by rw [a.gpr]; simp [bad], by rw [a.mem, mem]; simp only [bad, ite_false]; exact cleared, ?_,
      (rest.mono (by decide)).trans (a.rest (by decide))⟩
    rw [a.mem, mem]; exact Frame.refl _ _

theorem pp_body_scoped_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtScopedInput g bs s)
    (pre : PpPre g s)
    (cleared : Spec.Rsa.wordsAt s.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) :
    WP isa body s fun t =>
      t.gpr .r0 = (if ppGood g bs then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) =
        (if ppGood g bs then ppValues g bs else List.replicate (ppPreWords g) 0) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, 8 * ppPreWords g⟩]) s.mem t.mem ∧
      Rest roundClobbers s t := by
  have preE : PpPre g (crtExpanded s g.base g.words) :=
    ⟨pre.fit, (by obtain ⟨r, hr, hc⟩ := pre.write; exact ⟨r, List.mem_append_right _ hr, hc⟩), pre.workspace, pre.stack, pre.sources, pre.input, pre.qi⟩
  obtain ⟨tr, t, run, r0, words, frame, rest⟩ := pp_body_ok _ h.body preE cleared
  obtain ⟨write, read⟩ := crt_expanded_covers h.workspace h.body.buffers.storageFits
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, r0, words, frame, ?_⟩
  · simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen run read write
  · exact ⟨rest.gpr, rfl, rfl, rest.sp⟩

end VG.Proof.Bignum.Arm
