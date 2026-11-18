module

public import VerifiedGarbage.Proof.MlKem.Arm.Reduce
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.Arm.Keccak
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlKem.Arm.Sample
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.Arm.Sign.Hash`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.Sign.Keccak`, which only this module used -/

section

/-!
# ML-DSA signing on ARMv7: SHAKE256 through the sponge functions

As on x86-64: zeroing the Keccak state at `scratch` (`kzero_ok`, from ML-KEM's
`zeroWords_ok`), and the calls of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` on it, with the working space at `scratch + 200`
(`kabs_ok`, `kpad_ok`, `ksqz_ok`, from ML-KEM's call lemmas of the sponge
functions in their frames, `Proof/MlKem/Arm/Keccak.lean`), and that two runs
in the same layout leak the same (`kabs_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ok pad_ok squeeze_ok absorb_ct pad_ct squeeze_ct
  regA below Kept)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-! ## Checks -/

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  inB wbs (sc 0) 200 && inB wbs (sc 200) 640 && inB bs (sc 0) 200 && inB bs (sc 200) 640 &&
    sepB bs (sc 0) 200 (sc 200) 640

/-- A piece of `len` bytes at `src` that `vg_keccak_absorb` reads. -/
def kabsChk (bs : List (Reg × Nat)) (src : Ptr) (len : Nat) : Bool :=
  inB bs src len && decide (src.1 ∈ bases) && decide (0 < len) && sepB bs src len (sc 0) 200 &&
    sepB bs src len (sc 200) 640

/-- The `len` bytes at `dst` that `vg_keccak_squeeze` writes. -/
def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  inB wbs dst len && inB bs dst len && decide (dst.1 ∈ bases) && decide (0 < len) && sepB bs (sc 0) 200 dst len &&
    sepB bs dst len (sc 200) 640

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem kChk_spec {bs wbs : List (Reg × Nat)} (h : kChk bs wbs = true) :
    inB wbs (sc 0) 200 = true ∧ inB wbs (sc 200) 640 = true ∧ inB bs (sc 0) 200 = true ∧
      inB bs (sc 200) 640 = true ∧ sepB bs (sc 0) 200 (sc 200) 640 = true := by
  simp only [kChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem kabsChk_spec {bs : List (Reg × Nat)} {src : Ptr} {len : Nat} (h : kabsChk bs src len = true) :
    inB bs src len = true ∧ src.1 ∈ bases ∧ 0 < len ∧ sepB bs src len (sc 0) 200 = true ∧
      sepB bs src len (sc 200) 640 = true := by
  simp only [kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ksqzChk_spec {bs wbs : List (Reg × Nat)} {dst : Ptr} {len : Nat} (h : ksqzChk bs wbs dst len = true) :
    inB wbs dst len = true ∧ inB bs dst len = true ∧ dst.1 ∈ bases ∧ 0 < len ∧
      sepB bs (sc 0) 200 dst len = true ∧ sepB bs dst len (sc 200) 640 = true := by
  simp only [ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The 8 bytes of stack of a call of a sponge function, apart from the layout. -/
theorem k8 {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) {p : Ptr} {l : Nat}
    (h : inB (rbs ++ wbs) p l = true) (hsp : s1.sp = s.sp) : (below s1 8).Disjoint ⟨pa s p, l⟩ := by
  show (belowA s1.sp 8).Disjoint _
  rw [hsp]; exact (L.stkD h).sub_left (belowA_sub hD)

/-- What the sponge functions leave, as `PostB`. -/
theorem postB_kept {s s1 s' : State} (hD : 8 ≤ D) (k : Keep argRegs s s1) {rs : List Region} {W : List Region}
    (hk : Kept (rs ++ [below s1 8]) s1 s') (hW : ∀ r ∈ rs, r ∈ W) : PostB D s s' W ∧ CS s s' := by
  have hcs : CS s s' := fun r hr hl => (hk.cs r hr hl).trans (k.cs r hr hl)
  refine ⟨⟨hk.rd.trans k.rd, hk.wr.trans k.wr, fun r hr => hcs r (bases_cs r hr).1 (bases_cs r hr).2,
    hk.sp.trans k.sp, ?_⟩, hcs⟩
  rw [← k.mem]
  refine hk.frame.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ (hW r hr), fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    show Region.Sub (belowA s1.sp 8) _
    rw [k.sp]; exact belowA_sub hD

/-! ## Zeroing the state -/

theorem kzero_ok {s : State} (L : Lay D rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true) :
    WP isa (.block kzero) s fun s' => PPostB D s s' [(sc 0, 200)] ∧ CS s s' ∧
      stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero := by
  obtain ⟨w0, _, i0, _, _⟩ := kChk_spec hk
  rw [kzero, VG.Impl.MlKem.Arm.zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = s.gpr .r7 := by rw [g]; simp [State.setReg]
  have ep : State.addr (s.gpr .r7) = pa s (sc 0) := by simp [pa]
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; have := L.nwp i0; simpa using this) fun k hk => by
      rw [e7, wr, ep]
      exact inRegions_sub (L.iW w0) (by omega_using [hk]) (by decide))
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7, ep] at hf hz
  have hcs : CS s s₂ := fun r hr hl => by
    rw [h₂.gpr, g]
    simp [State.setReg, ne12_pres r hr hl]
  refine ⟨PostB.of_cs hcs (by rw [h₂.rd, rd]) (by rw [h₂.wr, wr]) (by rw [h₂.sp, sp]) (by rw [← m]; exact hf),
    hcs, VG.Proof.MlKem.Arm.Sample.stateAt_zero hz⟩

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .r7 = y.gpr .r7) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  block_tr (rs := [.r7]) (by decide) fun x y hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h x y hp

/-! ## Absorbing -/

theorem kabsOk {src : Ptr} {len rate pos : Nat} (b1 : src.1 ∈ bases) :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem kabsArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)] s s1)
    (k : Keep argRegs s s1) :
    AbsorbArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr src.1 + BitVec.ofNat 32 src.2) rate pos len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨is, _, l0, d0, d1⟩ := kabsChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt is
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = pa s src := L.pa32 is l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, hpos, hl, by rw [k.sp]; have := L.sp; omega_using [hD, this],
    L.fit (p := sc 0) i0 (by decide), L.fit is l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a0, as]; exact L.disj d0
  · simp only [regA, a1, as]; exact L.disj d1
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, as]; exact k8 L hD is k.sp
  · simp only [regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)
  · simp only [regA, as]; rw [k.rd, k.wr]; exact L.cR is

theorem kabs_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    WP isa (kabs src len rate pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ CS s s' ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        Repr s'.mem (pa s (sc 0)) rate (msg ++ bytesAt s.mem (pa s src) len) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨is, b1, l0, _, _⟩ := kabsChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (kabsOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = pa s src := L.pa32 is l0
  refine absorb_ok (kabsArgs L hD hk hc hrate hpos hA k) fun s' hkept hR _ => ?_
  simp only [regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0, as] at hR
  exact hR msg hmsg hpos'

theorem kabs_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len rate pos : Nat}
    (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    RelCT isa (LRel D rbs wbs) (kabs src len rate pos) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  obtain ⟨is, b1, _, _, _⟩ := kabsChk_spec hc
  refine RelCT.seq (setArgs_rel (kabsOk b1)) (absorb_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, kabsArgs R.lx hD hk hc hrate hpos hAx kx, ?_⟩
  rw [R.eq i0, R.eq is]
  exact kabsArgs R.ly hD hk hc hrate hpos hAy ky

/-! ## Padding -/

theorem kpadOk {rate pos suffix : Nat} :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok]

/-- The moves of `pad`'s arguments. -/
theorem kpadMoves_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr] as)) s fun s1 =>
      (∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip as, s1.gpr da.1 = da.2.val s) ∧ Keep argRegs s s1 :=
  WP.mono (setArgsTo_ok _ as (by decide) (by decide) ha s) fun _ ⟨h, k⟩ => ⟨h, k.mono (by decide)⟩

theorem kpadArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate)
    (hA : ∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
      s1.gpr da.1 = da.2.val s)
    (k : Keep argRegs s s1) :
    PadArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200) rate pos (BitVec.ofNat 32 suffix) := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine ⟨hA (.r0, .ptr (sc 0)) (by simp), hA (.r1, .imm rate) (by simp), hA (.r2, .imm pos) (by simp),
    hA (.r3, .imm suffix) (by simp), hA (.lr, .ptr (sc 200)) (by simp), hrate, hpos, by rw [k.sp]; have := L.sp; omega_using [hD, this],
    L.fit (p := sc 0) i0 (by decide), L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)

theorem b8_ofNat32 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 32 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem kpad_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    WP isa (kpad rate pos suffix) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ CS s s' ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  refine WP.seq (WP.mono (kpadMoves_ok _ kpadOk s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine pad_ok (kpadArgs L hD hk hrate hpos hA k) fun s' hkept hR => ?_
  simp only [regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0] at hR
  rw [hR msg hmsg hpos', b8_ofNat32 hs]

theorem kpad_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {rate pos suffix : Nat} (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    RelCT isa (LRel D rbs wbs) (kpad rate pos suffix) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  have hm : RelCT isa (LRel D rbs wbs) (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr]
      [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)])) fun x1 y1 => ∃ x y, LRel D rbs wbs x y ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        x1.gpr da.1 = da.2.val x) ∧ Keep argRegs x x1) ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        y1.gpr da.1 = da.2.val y) ∧ Keep argRegs y y1) :=
    RelCT.mono (RelCT.wpDep (block_nomem_tr (setArgsTo_nomem _ _))
      (fun x y _ => ⟨kpadMoves_ok _ kpadOk x, kpadMoves_ok _ kpadOk y⟩)) (fun _ _ h => h)
      fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩
  refine RelCT.seq hm (pad_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, kpadArgs R.lx hD hk hrate hpos hAx kx, ?_⟩
  rw [R.eq i0]
  exact kpadArgs R.ly hD hk hrate hpos hAy ky

/-! ## Squeezing -/

theorem ksqzOk {dst : Ptr} {len rate : Nat} (b1 : dst.1 ∈ bases) :
    [Arg.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ksqzArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates)
    (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)] s s1)
    (k : Keep argRegs s s1) :
    SqueezeArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr dst.1 + BitVec.ofNat 32 dst.2) rate 0 len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨wd, id, _, l0, d0, d1⟩ := ksqzChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt id
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = pa s dst := L.pa32 id l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, Nat.zero_le _, hl, by rw [k.sp]; have := L.sp; omega_using [hD, this],
    L.fit (p := sc 0) i0 (by decide), L.fit id l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, ad]; exact L.disj d0
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a1, ad]; exact L.disj d1
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, ad]; exact k8 L hD id k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, a0, a1, ad]; rw [k.wr]; exact Covers.cons (L.cW w0) (Covers.cons (L.cW wd) (L.cW w1))

theorem ksqz_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    WP isa (ksqz rate dst len) s fun s' => PPostB D s s' [(sc 0, 200), (dst, len), (sc 200, 640)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s dst) len = squeezeFrom rate (stateAt s.mem (pa s (sc 0))) 0 len := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨wd, id, b1, l0, _, _⟩ := ksqzChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (ksqzOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = pa s dst := L.pa32 id l0
  refine squeeze_ok (ksqzArgs L hD hk hc hrate hA k) fun s' hkept ho _ _ => ?_
  simp only [regA, a0, a1, ad] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (dst, len), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, ?_⟩
  rw [ad, a0, k.mem] at ho
  exact ho

theorem ksqz_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {dst : Ptr} {len rate : Nat}
    (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    RelCT isa (LRel D rbs wbs) (ksqz rate dst len) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  obtain ⟨_, id, b1, _, _, _⟩ := ksqzChk_spec hc
  refine RelCT.seq (setArgs_rel (ksqzOk b1)) (squeeze_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, ksqzArgs R.lx hD hk hc hrate hAx kx, ?_⟩
  rw [R.eq i0, R.eq id]
  exact ksqzArgs R.ly hD hk hc hrate hAy ky

end

end VG.Proof.MlDsa.Arm.Sign

end

end


/-!
# ML-DSA signing on ARMv7: `H` of pieces of memory

`shakeAt ps out len` zeroes the Keccak state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: `H` of their concatenation (`shake_ok`),
leaking only the addresses (`shake_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : Spec.Sha3.State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d) = SHAKE256(s, 8d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (m : List Byte) (d : Nat) : H m d = squeezeFrom 136 (padded 136 (BitVec.ofNat 8 0x1f) m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  kabsChk bs p.1 p.2 && decide (p.1.1 ∈ bases)

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pieces, List.flatMap_cons, List.length_append, VG.Proof.MlKem.bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem pieceChk_keep {p : Ptr × Nat} (h : pieceChk (rbs ++ wbs) p = true) :
    keepB (rbs ++ wbs) [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [pieceChk, kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hin, _⟩, _⟩, s1⟩, s2⟩, hcs⟩ := h
  simp only [keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

theorem pieces_keep {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) :
    ∀ {ps : List (Ptr × Nat)}, (∀ p ∈ ps, keepB (rbs ++ wbs) ws p.1 p.2 = true) → pieces s' ps = pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hcs_trans {s s₁ s₂ : State} (h₁ : CS s s₁) (h₂ : CS s₁ s₂) : CS s s₂ := CS.trans h₁ h₂

theorem bases_all : ∀ w ∈ [((sc 0 : Ptr), 200), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
  decide

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (D : Nat) (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ (s : State) (_ : Lay D rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      CS s s' ∧ Repr s'.mem (pa s (sc 0)) rate (msg ++ pieces s ps)

theorem absAll_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) : ∀ (ps : List (Ptr × Nat)), AbsOk D rbs wbs rate ps
  | [] => fun _ _ _ _ _ _ _ hR => WP.block_nil ⟨PostB.refl _ _ _, fun _ _ _ => rfl, by simpa using hR⟩
  | (p, l) :: ps => by
    intro s L pos msg hps hpos hm hR
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    refine WP.seq (WP.mono (kabs_ok L hD hk hkc hrate hpos) fun s₁ ⟨hP₁, hc₁, hR₁⟩ => ?_)
    have L₁ := L.post hP₁ hcs
    have e0 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
    have hR₁' := hR₁ msg hR hm
    rw [← e0] at hR₁'
    have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (pa s p) l).length % rate := by
      rw [List.length_append, VG.Proof.MlKem.bytesAt_length, hm, Nat.mod_add_mod]
    refine WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (pa s p) l) hps.2
      (Nat.mod_lt _ hr0) h3 hR₁') fun s₂ ⟨hP₂, hc₂, hR₂⟩ =>
        ⟨PPostB.trans hP₁ hP₂ bases_all (fun w hw => hw) (fun w hw => hw), hcs_trans hc₁ hc₂, ?_⟩
    rw [e0, pieces_keep L hP₁ fun q hq => pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
    simpa only [pieces, List.flatMap_cons, List.append_assoc] using hR₂

/-- The output: `len` bytes to `out`. -/
def shakeChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (out : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && ps.all (pieceChk bs) && ksqzChk bs wbs out len

theorem shakeChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {out : Ptr} {len : Nat}
    (h : shakeChk bs wbs ps out len = true) :
    kChk bs wbs = true ∧ ps.all (pieceChk bs) = true ∧ ksqzChk bs wbs out len = true := by
  simp only [shakeChk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem shake_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) {s : State} (L : Lay D rbs wbs s) :
    WP isa (shakeAt ps out len) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      CS s s' ∧ bytesAt s'.mem (pa s out) len = H (pieces s ps) len := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hocs : out.1 ∈ bases := (ksqzChk_spec hsq).2.2.1
  have hrate : (136 : Nat) ∈ rates := by decide
  refine WP.seq (WP.mono (kzero_ok L hk) fun s₁ ⟨hP₁, hc₁, hz⟩ => ?_)
  have L₁ := L.post hP₁ hcs
  have e1 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : pieces s₁ ps = pieces s ps := pieces_keep L hP₁ hpk
  refine WP.seq (WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ 0 [] hps (by decide) rfl
    (by rw [e1]; exact repr_nil hz)) fun s₂ ⟨hP₂, hc₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂ hcs
  have e2 : pa s₂ (sc 0) = pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (kpad_ok L₂ hD hk hrate (pos := totLen ps % 136) (Nat.mod_lt _ (by decide))
    (show 0x1f < 256 by decide)) fun s₃ ⟨hP₃, hc₃, hS₃⟩ => ?_)
  have L₃ := L₂.post hP₃ hcs
  have e3 : pa s₃ (sc 0) = pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (pieces s ps) (by rw [e2]; exact hR₂) (by rw [pieces_length])
  refine WP.mono (ksqz_ok L₃ hD hk hsq hrate) fun s₄ ⟨hP₄, hc₄, ho⟩ => ?_
  have eo : pa s₃ out = pa s out := by rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  have h12 : PPostB D s s₂ [(sc 0, 200), (sc 200, 640)] :=
    PPostB.trans hP₁ hP₂ bases_all (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..)
      (fun w hw => hw)
  have h123 : PPostB D s s₃ [(sc 0, 200), (sc 200, 640)] := PPostB.trans h12 hP₃ bases_all (fun w hw => hw) (fun w hw => hw)
  have hcs4 : ∀ w ∈ [((sc 0 : Ptr), 200), (out, len), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    exacts [by decide, hocs, by decide]
  refine ⟨PPostB.trans h123 hP₄ hcs4 (fun w hw => ?_) (fun w hw => ?_),
    hcs_trans (hcs_trans (hcs_trans hc₁ hc₂) hc₃) hc₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  rw [← eo, ho, e3, hS, H_eq]

/-! ## Constant time -/

theorem LRel.step (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    (htr : RelCT isa (LRel D rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay D rbs wbs x → WP isa c x fun x' => ∃ W, PostB D x x' W) :
    RelCT isa (LRel D rbs wbs) c (LRel D rbs wbs) :=
  VG.Proof.MlDsa.Arm.Sign.postDep htr (F := fun x x' => ∃ W, PostB D x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  VG.Proof.MlDsa.Arm.Sign.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil)
    (F := fun x x' => x' = x) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem absAll_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate →
      RelCT isa (LRel D rbs wbs) (absAll rate ps pos) (LRel D rbs wbs)
  | [], _, _, _ => nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (kabs_tr hD hk hkc hrate hpos)
      fun x Lx => WP.mono (kabs_ok Lx hD hk hkc hrate hpos) fun _ h => ⟨_, h.1⟩)
      (absAll_tr hcs hD hk hrate ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem shake_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) :
    RelCT isa (LRel D rbs wbs) (shakeAt ps out len) (LRel D rbs wbs) := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hrate : (136 : Nat) ∈ rates := by decide
  have i0 : inB (rbs ++ wbs) (sc 0) 200 = true := (kChk_spec hk).2.2.1
  refine RelCT.seq (LRel.step hcs (kzero_tr fun x y h => h.eq i0)
    fun x Lx => WP.mono (kzero_ok Lx hk) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (absAll_tr hcs hD hk hrate ps 0 hps (by decide)) (RelCT.seq (LRel.step hcs
      (kpad_tr hD hk hrate (Nat.mod_lt _ (by decide)))
      fun x Lx => WP.mono (kpad_ok Lx hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
        fun _ h => ⟨_, h.1⟩)
      (LRel.step hcs (ksqz_tr hD hk hsq hrate) fun x Lx => WP.mono (ksqz_ok Lx hD hk hsq hrate) fun _ h => ⟨_, h.1⟩)))

end

end VG.Proof.MlDsa.Arm.Sign

end

end

/-!
# ML-DSA signing on ARMv7: the function's contract, layout, entry and exit

As on x86-64: the contract the proof is written against (`signK`, which the
shared contract implies), the layout of the function's buffers (`sk`, `mu`,
`rnd` read, in `r4`, `r5`, `r6`; `scratch` and `sig` written, in `r7` and
`r8`), what holds of the state throughout (`Top`: the permissions and the
stack pointer of entry, the pointers in their registers, and the caller's
`r4`–`r11` and `lr` saved in `scratch`), the prologue (`pro_ok`), the return
(`topEnd_ok`), branches on `r11` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences
of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (Saved SaveInv RestoreInv saveRegs_ok restoreRegs_ok)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- The prepared polynomials `cache` points to, if it is not 0. -/
abbrev cacheR (p : Params) (s : State) : Region := ⟨State.addr (stackArg s 1), cacheLen p⟩

/-- The regions of the prepared polynomials: none if `cache` is 0. -/
def cacheRd (p : Params) (s : State) : List Region := if stackArg s 1 = 0 then [] else [cacheR p s]

/-- If `cache` is not 0: the `ŝ₁ ‖ ŝ₂ ‖ t̂₀` of `sk`, apart from `sig`, `scratch`
and the stack. -/
def CachePre (p : Params) (D : Nat) (s : State) : Prop :=
  stackArg s 1 ≠ 0 →
    (cacheR p s).Disjoint ⟨State.addr (s.gpr .r3), p.sigLen⟩ ∧
    (cacheR p s).Disjoint ⟨State.addr (stackArg s 0), scrLen p⟩ ∧ (belowA s.sp D).Disjoint (cacheR p s) ∧
    (stackArg s 1).toNat + cacheLen p ≤ 2 ^ 32 ∧
    CachedSecretPolys p s.mem (State.addr (stackArg s 1)) (bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen)

/-- `vg_mldsa*_sign_with_cache(sk = r0, mu = r1, rnd = r2, sig = r3, scratch = [sp],
cache = [sp, #4]) -> r0`, with `D` bytes of stack, and the leakage `signLeak`. -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    let sk : Region := ⟨State.addr (s.gpr .r0), p.skLen⟩
    let mu : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let rnd : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r3), p.sigLen⟩
    let scr : Region := ⟨State.addr (stackArg s 0), scrLen p⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = sk :: mu :: rnd :: args :: cacheRd p s ∧ s.wr = [sig, scr] ∧
    sk.Disjoint sig ∧ sk.Disjoint scr ∧ mu.Disjoint sig ∧ mu.Disjoint scr ∧ rnd.Disjoint sig ∧
    rnd.Disjoint scr ∧ sig.Disjoint scr ∧ sig.Disjoint args ∧ scr.Disjoint args ∧
    (belowA s.sp D).Disjoint sk ∧ (belowA s.sp D).Disjoint mu ∧ (belowA s.sp D).Disjoint rnd ∧
    (belowA s.sp D).Disjoint sig ∧ (belowA s.sp D).Disjoint scr ∧
    (s.gpr .r0).toNat + p.skLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + scrLen p ≤ 2 ^ 32 ∧ D ≤ s.sp.toNat ∧
    s.sp.toNat + 8 ≤ 2 ^ 32 ∧ CachePre p D s
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen)
      (bytesAt s.mem (State.addr (s.gpr .r1)) 64) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)) (s'.gpr .r0)
      (bytesAt s'.mem (State.addr (s.gpr .r3)) p.sigLen)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ s₁.sp = s₂.sp ∧
    signLeak p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen) (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) 64)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r2)) 32) =
      signLeak p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen) (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) 64)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r2)) 32) ∧
    stackArg s₁ 1 = stackArg s₂ 1

/-! ## The contract of the entries -/

/-- The value of `cache` an entry passes. -/
def cacheV (p : Params) (prepared : Bool) (sk : BitVec 32) : BitVec 32 :=
  if prepared then sk + BitVec.ofNat 32 p.skLen else 0

/-- `vg_mldsa*_sign` or `vg_mldsa*_sign_prepared` (`sk = r0, mu = r1, rnd = r2,
sig = r3, scratch = [sp]) -> r0`, with `D` bytes of stack: `signK` with a
key of `keyLen` bytes satisfying `KeyOk`, and no `cache`. -/
def signE (p : Params) (prepared : Bool) (D : Nat) : Contract isa where
  pre s :=
    let sk : Region := ⟨State.addr (s.gpr .r0), secretKeyLen p prepared⟩
    let mu : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let rnd : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r3), p.sigLen⟩
    let scr : Region := ⟨State.addr (stackArg s 0), scrLen p⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sk, mu, rnd, args] ∧ s.wr = [sig, scr] ∧
    sk.Disjoint sig ∧ sk.Disjoint scr ∧ mu.Disjoint sig ∧ mu.Disjoint scr ∧ rnd.Disjoint sig ∧
    rnd.Disjoint scr ∧ sig.Disjoint scr ∧ sig.Disjoint args ∧ scr.Disjoint args ∧
    (belowA s.sp D).Disjoint sk ∧ (belowA s.sp D).Disjoint mu ∧ (belowA s.sp D).Disjoint rnd ∧
    (belowA s.sp D).Disjoint sig ∧ (belowA s.sp D).Disjoint scr ∧
    (s.gpr .r0).toNat + secretKeyLen p prepared ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + scrLen p ≤ 2 ^ 32 ∧ D ≤ s.sp.toNat ∧
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ SecretKeyOk p prepared s.mem (State.addr (s.gpr .r0))
  post := (signK p D).post
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ s₁.sp = s₂.sp ∧
    signLeak p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen) (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) 64)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r2)) 32) =
      signLeak p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen) (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) 64)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r2)) 32)

/-- The stack an entry uses: its frames (16 bytes), and the kernel's (28, `signStack`). -/
abbrev entryStack : Nat := 44

theorem secretKeyLen_ge (p : Params) (prepared : Bool) : p.skLen + (if prepared then cacheLen p else 0) ≤
    secretKeyLen p prepared := by
  cases prepared <;> simp [secretKeyLen, preparedSecretKeyBytes, cacheLen, n] <;> omega

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.r4, p.skLen), (.r5, 64), (.r6, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.r7, scrLen p), (.r8, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := sgR p ++ sgW p

/-- The pointer the function keeps in each register of `bases`, from its entry state. -/
def ptrOf (σ : State) : Reg → BitVec 32
  | .r7 => stackArg σ 0
  | .r9 => stackArg σ 1
  | .r4 => σ.gpr .r0
  | .r5 => σ.gpr .r1
  | .r6 => σ.gpr .r2
  | _ => σ.gpr .r3

theorem sgB_bases (p : Params) : ∀ b ∈ sgB p, b.1 ∈ bases := by
  intro b hb; simp only [sgB, sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ r ∈ bases, s.gpr r = ptrOf σ r
  saved : Saved s.mem (pa s (sc oSV)) σ.gpr
  savlr : s.mem.readW (pa s (sc (oSV + 32))) 32 = σ.gpr .lr

section
variable {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ)
include hp

theorem sgLay (hsz : scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay D (sgR p) (sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, -, -, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp, -⟩ := hp
  have e7 : s.gpr .r7 = stackArg σ 0 := h.regs .r7 (by decide)
  have e4 : s.gpr .r4 = σ.gpr .r0 := h.regs .r4 (by decide)
  have e5 : s.gpr .r5 = σ.gpr .r1 := h.regs .r5 (by decide)
  have e6 : s.gpr .r6 = σ.gpr .r2 := h.regs .r6 (by decide)
  have e8 : s.gpr .r8 = σ.gpr .r3 := h.regs .r8 (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    by rw [h.sp]; exact hsp⟩
  · intro b hb
    simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_arith
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e4, e5, e6, e7, e8]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8, h.sp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    exacts [n1, n2, n3, n5, n4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    · exact mem ⟨State.addr (σ.gpr .r0), p.skLen⟩ (List.mem_append_left _ (hrd ▸ List.mem_cons_self ..))
    · exact mem ⟨State.addr (σ.gpr .r1), 64⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r2), 32⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    · exact mem ⟨State.addr (stackArg σ 0), scrLen p⟩
        (List.mem_append_right _ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (List.mem_append_right _ (hwr ▸ List.mem_cons_self ..))
  · simp only [sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e7, e8]
    · exact memw ⟨State.addr (stackArg σ 0), scrLen p⟩ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact memw ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (hwr ▸ List.mem_cons_self ..)

end

theorem pa_add (s : State) (r : Reg) (a b : Nat) : pa s (r, a + b) = pa s (r, a) + BitVec.ofNat 64 b := by
  simp only [pa]; rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- The saved registers are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool := keepB bs ws (sc oSV) 36

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top σ s)
    (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws)
    (hc : topChk (rbs ++ wbs) ws = true) : Top σ s' := by
  have hs : ∀ k < 9, s'.mem.readW (pa s' (sc (oSV + 4 * k))) 32 = s.mem.readW (pa s (sc (oSV + 4 * k))) 32 :=
    fun k hk => L.keepW hP (keepB_sub hc (by simp [oSV]) (by simp [oSV]; omega_arith))
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp,
    fun r hr => (hP.bs _ hr).trans (h.regs r hr), fun i hi => ?_, ?_⟩
  · have e := hs i (by omega_arith)
    rw [pa_add, pa_add] at e
    rw [e]; exact h.saved i hi
  · have e := hs 8 (by omega_arith)
    rw [e]; exact h.savlr

/-! ## The prologue -/

theorem pro_eq : pro = ([.ldrSp .r12 0] : List Instr) ++ Impl.MlKem.Arm.saveRegs .r12 oSV ++
    ([.str .lr .r12 (oSV + 32), .mov .r7 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .mov .r11 (.imm 1)] : List Instr) := rfl

theorem scrLen_ge (p : Params) : 5120 ≤ scrLen p := by
  unfold scrLen scratchWords; omega_arith

/-- `Top` but for `r9`, which the prologue loads last. -/
structure Top0 (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ r ∈ bases, r ≠ .r9 → s.gpr r = ptrOf σ r
  saved : Saved s.mem (pa s (sc oSV)) σ.gpr
  savlr : s.mem.readW (pa s (sc (oSV + 32))) 32 = σ.gpr .lr

theorem pro0_ok {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ) :
    WP isa (.block pro) σ fun s => Top0 σ s ∧ Frame [⟨State.addr (stackArg σ 0), scrLen p⟩] σ.mem s.mem ∧
      s.gpr .r11 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n5, -⟩ := hp'
  have hge := scrLen_ge p
  have hS : (⟨State.addr (stackArg σ 0), scrLen p⟩ : Region) ∈ σ.wr := by rw [hwr]; simp
  have hA : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), by simp [stackArgAddr, Region.Contains]⟩
  rw [pro_eq, List.append_assoc, WP.block_append_iff]
  have hl : WP isa (.block [.ldrSp .r12 0]) σ fun s₁ => s₁.gpr .r12 = stackArg σ 0 ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = σ.gpr r) ∧ s₁.mem = σ.mem ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr ∧ s₁.sp = σ.sp := by
    run_block [hA, show (0 : Nat) < 4096 by decide]
    exact ⟨by simp [stackArg, stackArgAddr], fun r hr => by simp [hr], trivial⟩
  refine WP.mono hl fun s₁ ⟨h12, hr, hm, hrd₁, hwr₁, hsp₁⟩ => ?_
  rw [WP.block_append_iff]
  have wS : ∀ o n, o + n ≤ scrLen p → InRegions s₁.wr (State.addr (stackArg σ 0) + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr₁]; exact inRegions_sub ⟨_, hS, Region.contains_self _ _⟩ h (by omega_arith)
  refine WP.mono (saveRegs_ok .r12 (off := 840) (by decide) (by rw [h12]; omega_arith) fun i hi => by
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS _ _ (by omega_arith)) fun s₂ h₂ => ?_
  have g12 : s₂.gpr .r12 = stackArg σ 0 := by rw [h₂.gpr, h12]
  have e872 : State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32)) =
      State.addr (stackArg σ 0) + BitVec.ofNat 64 872 := by
    rw [g12]; exact addr_add (by simp only [oSV]; omega_arith)
  have i872 : InRegions s₂.wr (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32))) 4 := by
    rw [e872, h₂.wr]; exact wS _ _ (by omega_arith)
  have o1 : oSV + 32 < 4096 := by decide
  run_block [i872, o1]
  have g : ∀ r, r ≠ .r12 → s₂.gpr r = σ.gpr r := fun r hr' => by rw [h₂.gpr, hr r hr']
  have hne : ∀ i < 8, Impl.MlKem.Arm.savedRegs.getD i Reg.r4 ≠ Reg.r12 := by decide
  rw [e872]
  refine ⟨⟨by simp [h₂.rd, hrd₁], by simp [h₂.wr, hwr₁], by simp [h₂.sp, hsp₁], fun r hr h9 => ?_, fun i hi => ?_, ?_⟩,
    ?_, trivial⟩
  · simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl h9 | simp [ptrOf, g12, g]
  · simp only [pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep (Offset.sep _ (by simp only [oSV]; omega_arith)
      (by omega_arith) (by omega_arith)) (by decide)]
    have := h₂.saved i hi
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add] at this
    rw [show oSV = 840 from rfl, this, hr _ (hne i hi)]
  · simp only [pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [show oSV + 32 = 872 from rfl, Mem.readW_writeW_self32, g _ (by decide)]
  · have f₁ := h₂.frame
    rw [h12, hm] at f₁
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base _ (by omega_arith)

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ) :
    WP isa (.block (pro ++ ([.ldrSp .r9 4] : List Instr))) σ fun s => Top σ s ∧
      Frame [⟨State.addr (stackArg σ 0), scrLen p⟩] σ.mem s.mem ∧ s.gpr .r11 = 1 := by
  have hp' := hp
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, ha, -, -, -, -, -, -, -, -, -, -, -, h8, -⟩ := hp'
  rw [WP.block_append_iff]
  refine WP.mono (pro0_ok hp) fun s₁ ⟨h₁, hf₁, h11⟩ => ?_
  have hA : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.sp + BitVec.ofNat 32 4)) 4 :=
    ⟨_, List.mem_append_left _ (by rw [h₁.rd, hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), by
        rw [h₁.sp]; simp only [stackArgAddr, Region.Contains, Nat.mul_zero, show BitVec.ofNat 32 0 = 0 from rfl]
        rw [addr_add (k := 4) (by omega_using [h8])]; simp; have := (State.addr σ.sp).isLt; omega_using []⟩
  have h4 : (4 : Nat) < 4096 := by decide
  have hl : WP isa (.block [.ldrSp .r9 4]) s₁ fun s => s.gpr .r9 = s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 4)) 32 ∧
      (∀ r, r ≠ .r9 → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    run_block [hA, h4]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  refine WP.mono hl fun s ⟨g9, g, hm, hrd', hwr', hsp'⟩ => ?_
  have e9 : s.gpr .r9 = stackArg σ 1 := by
    rw [g9, h₁.sp, stackArg, stackArgAddr]
    refine hf₁.readW (r := ⟨stackArgAddr σ 0, 8⟩) ?_ ?_ (by decide)
    · simp only [stackArgAddr, Region.Contains, Nat.mul_zero, show BitVec.ofNat 32 0 = 0 from rfl]
      rw [addr_add (k := 4) (by omega_using [h8])]; simp; have := (State.addr σ.sp).isLt; omega_using []
    · intro r hr; rw [List.mem_singleton] at hr; subst hr; exact ha.symm
  have epa : ∀ o, pa s (sc o) = pa s₁ (sc o) := fun o => by simp only [pa, g .r7 (by decide)]
  refine ⟨⟨hrd'.trans h₁.rd, hwr'.trans h₁.wr, hsp'.trans h₁.sp, fun r hr => ?_, ?_, ?_⟩, by rw [hm]; exact hf₁,
    by rw [g _ (by decide)]; exact h11⟩
  · by_cases h9 : r = .r9
    · subst h9; exact e9
    · rw [g r h9]; exact h₁.regs r hr h9
  · rw [hm, epa]; exact h₁.saved
  · rw [hm, epa]; exact h₁.savlr

/-! ## The return -/

theorem topEnd_ok {σ s : State} (h : Top σ s) (hin : InRegions (s.rd ++ s.wr) (pa s (sc oSV)) 36)
    (hfit : (s.gpr .r7).toNat + 876 ≤ 2 ^ 32) :
    WP isa (.block Impl.MlKem.Arm.topEnd) s fun s' => s'.gpr .r0 = s.gpr .r11 ∧
      (∀ r ∈ preserved, s'.gpr r = σ.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  rw [Impl.MlKem.Arm.topEnd, List.append_assoc, WP.block_append_iff]
  have hk : WP isa (.block [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r11 ∧ s'.gpr .r3 = s.gpr .r7 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    run_block []
  refine WP.mono hk fun s₁ ⟨r0, r3, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 840 = pa s (sc oSV) := by rw [r3]; rfl
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 840) (by decide)
    (by rw [r3]; omega_arith) (g := σ.gpr) (by rw [e3, m₁]; exact h.saved)
    fun i hi => by
      rw [e3, rd₁, wr₁]
      exact inRegions_sub hin (by omega_arith) (by decide))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = s.gpr .r7 := by rw [h₂.other .r3 (by decide), r3]
  have e872 : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = pa s (sc (oSV + 32)) := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega_arith)
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₂.rd, h₂.wr, rd₁, wr₁, pa_add]
    exact inRegions_sub hin (by omega_arith) (by decide)
  have ho : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 (Impl.MlKem.Arm.oSave + 32)]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0]
  · by_cases e : r = .lr
    · subst e
      rw [lr, e872, h₂.mem, m₁]; exact h.savlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, Impl.MlKem.Arm.savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [m, h₂.mem, m₁]
  · rw [sp, h₂.sp, sp₁]

/-! ## Branches on `r11` -/

/-- The comparison of `r11` with 0 writes only the flags. -/
theorem cmp11_ok (s : State) (D : Nat) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => PPostB D s s₁ [] ∧ CS s s₁ ∧ s₁.mem = s.mem ∧
      s₁.z = (s.gpr .r11 == 0) := by
  have h : WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r11 == 0) := by
    run_block []
    simp
  refine WP.mono h fun s₁ ⟨g, m, rd, wr, sp, z⟩ => ?_
  have hcs : CS s s₁ := fun r _ _ => by rw [g]
  exact ⟨PostB.of_cs hcs rd wr sp (by rw [m]; exact Frame.refl _ _), hcs, m, z⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, PPostB D s s₁ [] → CS s s₁ → s₁.mem = s.mem → s.gpr .r11 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, PPostB D s s₁ [] → CS s s₁ → s₁.mem = s.mem → s.gpr .r11 = 0 → WP isa e s₁ Q) :
    WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (cmp11_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!(s.gpr .r11 == 0)) (show some (!s₁.z) = _ by rw [hz]) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → x.gpr .r11 = y.gpr .r11)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ CS x₀ x ∧ x.mem = x₀.mem) ∧
      (PPostB D y₀ y [] ∧ CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ CS x₀ x ∧ x.mem = x₀.mem) ∧
      (PPostB D y₀ y [] ∧ CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (PPostB D x x₁ [] ∧ CS x x₁ ∧ x₁.mem = x.mem) ∧ x₁.z = (x.gpr .r11 == 0))
    (fun x y _ => ⟨WP.mono (cmp11_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (cmp11_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((PPostB D x₀ x₁ [] ∧ CS x₀ x₁ ∧ x₁.mem = x₀.mem) ∧ x₁.z = (x₀.gpr .r11 == 0)) ∧
      ((PPostB D y₀ y₁ [] ∧ CS y₀ y₁ ∧ y₁.mem = y₀.mem) ∧ y₁.z = (y₀.gpr .r11 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show some (!x₁.z) = some (!y₁.z)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_arith) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega_arith]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega_arith) (by omega_arith)) s₁ h₁

/-- `seqOk`: each piece from `I k` to `I (k + 1)`, and `I k` kept by the
test of `r11` after it; it ends in `I k` after the last piece, or after the
first that leaves `r15 = 0`. -/
theorem seqOk_ok {D : Nat} {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a < k → k ≤ a + n → ∀ s s₁, I k s → PPostB D s s₁ [] →
        CS s s₁ → s₁.mem = s.mem → I k s₁) →
      (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqOk f a n) s fun s' => ∃ k, a ≤ k ∧ k ≤ a + n ∧ I k s' ∧
        (k = a + n ∨ (s'.gpr .r11) = 0)
  | 0, a, _, _, s, hs => WP.block_nil ⟨a, Nat.le_refl _, by omega_using [], hs, .inl rfl⟩
  | n + 1, a, hst, h, s, hs => by
    rw [seqOk]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_using []) s hs) fun s₁ h₁ => ?_)
    refine ifOkElse_ok (D := D) (fun s₂ hP hcs hm _ => ?_) fun s₂ hP hcs hm he => ?_
    · refine WP.mono (seqOk_ok n (a + 1) (fun k hk hk' => hst k (by omega_using [hk]) (by omega_using [hk']))
        (fun k hk hk' => h k (by omega_using [hk]) (by omega_using [hk'])) s₂ (hst _ (by omega_using []) (by omega_using []) _ _ h₁ hP hcs hm))
        fun s' ⟨k, hk, hk', hI, hk''⟩ => ⟨k, by omega_using [hk], by omega_using [hk'], hI, hk''.imp (fun _ => by omega_arith) id⟩
    · exact WP.block_nil ⟨a + 1, by omega_using [], by omega_using [], hst _ (by omega_using []) (by omega_using []) _ _ h₁ hP hcs hm,
        .inr (by rw [hcs _ (by decide) (by decide)]; exact he)⟩

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega_arith]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega_arith)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega_arith) (by omega_arith))

end VG.Proof.MlDsa.Arm.Sign
