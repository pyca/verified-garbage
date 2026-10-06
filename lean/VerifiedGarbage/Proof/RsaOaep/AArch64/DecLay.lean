import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# RSAES-OAEP decryption on AArch64: where everything is

As for RSAES-PKCS1-v1_5 (`Proof/RsaPkcs1Enc/AArch64/DecLay.lean`): the
function's buffers and its stack, from the inner frame's base `Q` (`DLay`):
below it the `P` bytes the calls use (`LOW`), from it the inner frame (`FR`),
the frame holding our return address (`LR`, from `Q + 272`) and our stack
arguments (`ARGS`, from `Q + 288`). `DLay.Ok` is what the shared contract
says of them. `Ctx` is what holds between the frames' pushes and pops: the
frame's words are followed by the pieces' own `Rep`, and every piece's
`Step` keeps `Ctx` (`Ctx.step`). From `Ctx` and the slots, the pieces'
`Lay`, `LabAt` and `OutAt` (`Ctx.lay`, `Ctx.labAt`, `Ctx.outAt`).
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (q_add add_add)

/-- The arguments, the inner frame's base `Q` and the bytes `P` below it the
calls use. -/
structure DLay where
  out : Addr
  ol : BitVec 64
  ml : Addr
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  p : Addr
  pl : BitVec 64
  q : Addr
  ql : BitVec 64
  dp : Addr
  dpl : BitVec 64
  dq : Addr
  dql : BitVec 64
  qi : Addr
  qil : BitVec 64
  lab : Addr
  labl : BitVec 64
  ct : Addr
  cl : BitVec 64
  scr : Addr
  sl : BitVec 64
  Q : Addr
  P : Nat

namespace DLay

variable (L : DLay)

abbrev OUT : Region := ⟨L.out, L.k.toNat⟩
abbrev ML : Region := ⟨L.ml, 8⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev PP : Region := ⟨L.p, L.pl.toNat⟩
abbrev QQ : Region := ⟨L.q, L.ql.toNat⟩
abbrev DP : Region := ⟨L.dp, L.pl.toNat⟩
abbrev DQ : Region := ⟨L.dq, L.ql.toNat⟩
abbrev QI : Region := ⟨L.qi, L.pl.toNat⟩
abbrev LAB : Region := ⟨L.lab, L.labl.toNat⟩
abbrev CT : Region := ⟨L.ct, L.k.toNat⟩
abbrev SCR : Region := ⟨L.scr, L.sl.toNat * 8⟩
abbrev FR : Region := ⟨L.Q, frameBytes⟩
abbrev LR : Region := ⟨L.Q + BitVec.ofNat 64 272, 16⟩
abbrev ARGS : Region := ⟨L.Q + BitVec.ofNat 64 288, 120⟩
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 288⟩

/-- The buffers the function only reads. -/
def ro : List Region := [L.N, L.E, L.PP, L.QQ, L.DP, L.DQ, L.QI, L.LAB, L.CT]

/-- What the contract says of where the buffers and the stack are, and of
the lengths. -/
structure Ok : Prop where
  /-- `out`, `msg_len` and `scratch` miss each other and every other buffer. -/
  oM : L.OUT.Disjoint L.ML
  oS : L.OUT.Disjoint L.SCR
  mS : L.ML.Disjoint L.SCR
  oR : ∀ R ∈ L.ro, L.OUT.Disjoint R
  mR : ∀ R ∈ L.ro, L.ML.Disjoint R
  sR : ∀ R ∈ L.ro, L.SCR.Disjoint R
  oA : L.OUT.Disjoint L.ARGS
  mA : L.ML.Disjoint L.ARGS
  sA : L.SCR.Disjoint L.ARGS
  /-- The stack misses every buffer. -/
  kO : L.STK.Disjoint L.OUT
  kM : L.STK.Disjoint L.ML
  kS : L.STK.Disjoint L.SCR
  kR : ∀ R ∈ L.ro, L.STK.Disjoint R
  /-- No buffer wraps. -/
  bO : L.out.toNat + L.k.toNat ≤ 2 ^ 64
  bM : L.ml.toNat + 8 ≤ 2 ^ 64
  bS : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  bR : ∀ R ∈ L.ro, R.base.toNat + R.len ≤ 2 ^ 64
  nQ : L.Q.toNat + 408 ≤ 2 ^ 64
  pQ : L.P ≤ L.Q.toNat
  /-- The lengths. -/
  kv : Spec.Rsa.lenValid L.k.toNat
  olk : L.ol.toNat = L.k.toNat
  clk : L.cl.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  pl1 : 1 ≤ L.pl.toNat
  plk : L.pl.toNat < L.k.toNat
  ql1 : 1 ≤ L.ql.toNat
  qlk : L.ql.toNat < L.k.toNat
  dpl : L.dpl.toNat = L.pl.toNat
  qil : L.qil.toNat = L.pl.toNat
  dql : L.dql.toNat = L.ql.toNat
  slk : Spec.RsaPss.scratchWords L.k.toNat ≤ L.sl.toNat

end DLay

theorem ro_N (L : DLay) : L.N ∈ L.ro := by simp [DLay.ro]
theorem ro_E (L : DLay) : L.E ∈ L.ro := by simp [DLay.ro]
theorem ro_PP (L : DLay) : L.PP ∈ L.ro := by simp [DLay.ro]
theorem ro_QQ (L : DLay) : L.QQ ∈ L.ro := by simp [DLay.ro]
theorem ro_DP (L : DLay) : L.DP ∈ L.ro := by simp [DLay.ro]
theorem ro_DQ (L : DLay) : L.DQ ∈ L.ro := by simp [DLay.ro]
theorem ro_QI (L : DLay) : L.QI ∈ L.ro := by simp [DLay.ro]
theorem ro_LAB (L : DLay) : L.LAB ∈ L.ro := by simp [DLay.ro]
theorem ro_CT (L : DLay) : L.CT ∈ L.ro := by simp [DLay.ro]

/-- A range within a writable buffer. -/
def InW (L : DLay) (R : Region) : Prop := Region.Sub R L.OUT ∨ Region.Sub R L.ML ∨ Region.Sub R L.SCR

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

namespace DLay.Ok

variable {L : DLay} (h : L.Ok)
include h

theorem k64 : 64 ≤ L.k.toNat := h.kv.1
theorem k1024 : L.k.toNat ≤ 1024 := h.kv.2

/-- `scratch` holds our 8192 bytes and the private-key operation's. -/
theorem s8192 : 8192 + Spec.Rsa.scratchWords L.k.toNat * 8 ≤ L.sl.toNat * 8 := by
  have := h.slk; unfold Spec.RsaPss.scratchWords at this; omega

omit h in
/-- A range in our stack is in `STK`. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ 288) : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [q_add L.Q L.P d]; exact Offset.sub_base _ (by omega)

omit h in
theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega)

/-- A range in our frames misses the stack the calls use. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 408) : Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by have := h.nQ; have := h.pQ; omega)

/-- Two ranges in our frames and arguments, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 408) (h₂ : d' + n' ≤ 408) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ ⟨L.Q + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ hs (by have := h.nQ; omega) (by have := h.nQ; omega)

/-- A range in our frames misses the writable buffers. -/
theorem stk_buf {d n : Nat} (hd : d + n ≤ 288) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs := sub_stk (L := L) hd
  rcases hR with hR | hR | hR
  · exact (h.kO.sub_left hs).sub_right hR
  · exact (h.kM.sub_left hs).sub_right hR
  · exact (h.kS.sub_left hs).sub_right hR

/-- A range in our stack arguments misses the writable buffers. -/
theorem args_buf {d n : Nat} (h₁ : 288 ≤ d) (h₂ : d + n ≤ 408) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  rcases hR with hR | hR | hR
  · exact (h.oA.symm.sub_left hs).sub_right hR
  · exact (h.mA.symm.sub_left hs).sub_right hR
  · exact (h.sA.symm.sub_left hs).sub_right hR

/-- Our part of `scratch`. -/
theorem ours_scr : Region.Sub ⟨L.scr, oRsa⟩ L.SCR := Region.sub_prefix (by have := h.s8192; unfold oRsa; omega)

omit h in
/-- The 16 bytes below the frame, where the hash functions save their
return address, in the stack the calls use. -/
theorem ret_low (hP : 16 ≤ L.P) : Region.Sub (retR L.Q) L.LOW := Offset.sub_below _ hP (by omega)

/-- The pieces' geometry. -/
theorem geo (hP : 16 ≤ L.P) : Geo L.Q L.scr where
  F16 := by have := h.pQ; omega
  Fw := by have := h.nQ; unfold frameBytes; omega
  Sw := by have := h.bS; have := h.s8192; unfold oRsa; omega
  dFS := by
    have hf := sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact (h.kS.sub_left hf).sub_right h.ours_scr
  dRS := (h.kS.sub_left (sub_trans (DLay.Ok.ret_low (L := L) hP) low_stk)).sub_right h.ours_scr
  dRF := by
    have := h.fr_low (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at this
    exact (this.sub_right (DLay.Ok.ret_low (L := L) hP)).symm

end DLay.Ok

/-! ## Between the frames' pushes and pops -/

/-- Our stack argument `j`. -/
def ourArg (L : DLay) : Nat → BitVec 64
  | 0 => L.pl | 1 => L.q | 2 => L.ql | 3 => L.dp | 4 => L.dpl | 5 => L.dq | 6 => L.dql | 7 => L.qi
  | 8 => L.qil | 9 => L.lab | 10 => L.labl | 11 => L.ct | 12 => L.cl | 13 => L.scr | _ => L.sl

/-- The state between the slots' writes and the frames' pops: `g` and `vv`
are the registers on entry, `m₀` the memory. -/
structure Ctx (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.PP, L.QQ, L.DP, L.DQ, L.QI, L.LAB, L.CT, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.ML, L.SCR]
  sp : t.sp = L.Q
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  lr : t.mem.readW (L.Q + BitVec.ofNat 64 272) 64 = g .x30
  args : ∀ j < 15, t.mem.readW (L.Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = ourArg L j
  frame : Frame [L.OUT, L.ML, L.SCR, L.STK] m₀ t.mem

/-- The slots of our arguments, as the frame's words `W`. -/
structure Slots (L : DLay) (W : Nat → BitVec 64) : Prop where
  scr : W 12 = L.scr
  out : W 19 = L.out
  n : W 20 = L.n
  k : W 21 = L.k
  e : W 22 = L.e
  el : W 23 = L.el
  sl : W 24 = L.sl
  lab : W 25 = L.lab
  labl : W 26 = L.labl
  ml : W 27 = L.ml

theorem Slots.of {L : DLay} {W W' : Nat → BitVec 64} (h : Slots L W)
    (hW : ∀ j, 12 ≤ j → j ≤ 27 → (j = 12 ∨ 19 ≤ j) → W' j = W j) : Slots L W' :=
  ⟨(hW 12 (by decide) (by decide) (by decide)).trans h.scr, (hW 19 (by decide) (by decide) (by decide)).trans h.out,
    (hW 20 (by decide) (by decide) (by decide)).trans h.n, (hW 21 (by decide) (by decide) (by decide)).trans h.k,
    (hW 22 (by decide) (by decide) (by decide)).trans h.e, (hW 23 (by decide) (by decide) (by decide)).trans h.el,
    (hW 24 (by decide) (by decide) (by decide)).trans h.sl, (hW 25 (by decide) (by decide) (by decide)).trans h.lab,
    (hW 26 (by decide) (by decide) (by decide)).trans h.labl, (hW 27 (by decide) (by decide) (by decide)).trans h.ml⟩

namespace Ctx

variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hc in
/-- The words `Ctx` keeps miss what a step writes. -/
theorem kept_apart (hP : 16 ≤ L.P) {ws : List Region} (hws : ∀ r ∈ ws, r = L.OUT ∨ r = L.ML) {d : Nat}
    (hd : 272 ≤ d) (hd₂ : d + 8 ≤ 288 ∨ 288 ≤ d) (hd' : d + 8 ≤ 408) :
    ∀ r ∈ ⟨L.Q, frameBytes⟩ :: ⟨L.scr, oRsa⟩ :: retR L.Q :: ws, Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ r := by
  have hb : ∀ R, InW L R → Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun R hR =>
    hd₂.elim (fun h₁ => hL.stk_buf h₁ hR) fun h₁ => hL.args_buf h₁ hd' hR
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · have := hL.fr_sep (d := d) (n := 8) (d' := 0) (n' := frameBytes) (by unfold frameBytes; omega) hd'
      (by decide)
    rwa [BitVec.add_zero] at this
  · exact hb _ (.inr (.inr hL.ours_scr))
  · exact (hL.fr_low hd').sub_right (DLay.Ok.ret_low (L := L) hP)
  · rcases hws r hr with rfl | rfl
    · exact hb _ (.inl fun _ h => h)
    · exact hb _ (.inr (.inl fun _ h => h))

/-- A piece's `Step`, writing only `out` and `*msg_len` outside the frame and
our working space, keeps `Ctx`. -/
theorem step (hP : 16 ≤ L.P) {ws : List Region} (hS : Step L.Q L.scr ws t t')
    (hws : ∀ r ∈ ws, r = L.OUT ∨ r = L.ML) : Ctx L g vv m₀ t' := by
  have hk : ∀ d, 272 ≤ d → (d + 8 ≤ 288 ∨ 288 ≤ d) → d + 8 ≤ 408 →
      t'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ h₃ => hS.frame.readW (Region.contains_self _ _) (kept_apart hL hP hws h₁ h₂ h₃) (by decide)
  refine ⟨hS.rd.trans hc.rd, hS.wr.trans hc.wr, hS.sp.trans hc.sp,
    fun r hr h30 => (hS.cs r hr h30).trans (hc.cs r hr h30), fun r hr => (hS.vec r hr).trans (hc.vs r hr),
    (hk 272 (by decide) (by decide) (by decide)).trans hc.lr,
    fun j hj => (hk _ (by omega) (by omega) (by omega)).trans (hc.args j hj), hc.frame.trans (hS.frame.sub fun r hr => ?_)⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · have hf := DLay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact ⟨L.STK, by simp, hf⟩
  · exact ⟨L.SCR, by simp, hL.ours_scr⟩
  · exact ⟨L.STK, by simp, sub_trans (DLay.Ok.ret_low (L := L) hP) DLay.Ok.low_stk⟩
  · rcases hws r hr with rfl | rfl
    · exact ⟨L.OUT, by simp, fun _ h => h⟩
    · exact ⟨L.ML, by simp, fun _ h => h⟩

/-- The pieces' `Lay`. -/
theorem lay (hP : 16 ≤ L.P) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W)
    (hW : W 12 = L.scr) : Lay t L.Q L.scr where
  sp := hc.sp
  fr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.FR, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  sc := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨L.SCR, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by
      have := hL.s8192; show 0 + oRsa ≤ L.sl.toNat * 8; unfold oRsa; omega⟩
  slot := by
    have := R.fr 12 (by decide)
    rw [hW] at this
    exact this
  geo := hL.geo hP

/-- Where the label is, for the label's hash. -/
theorem labAt (hP : 16 ≤ L.P) {W : Nat → BitVec 64} (hS : Slots L W) :
    LabAt t L.Q L.scr W L.lab L.labl.toNat where
  hl := hS.lab
  hll := by rw [hS.labl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  len := L.labl.isLt
  cov := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.LAB, by rw [hc.rd]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  dS := ((hL.sR _ (ro_LAB L)).sub_left hL.ours_scr).symm
  dF := by
    have hf := DLay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact ((hL.kR _ (ro_LAB L)).sub_left hf).symm
  dK := (hL.kR _ (ro_LAB L)).sub_left (sub_trans (DLay.Ok.ret_low (L := L) hP) DLay.Ok.low_stk)

omit hc in
/-- A writable buffer, apart from the frame, our working space and the 16
bytes below the frame. -/
theorem apart (hP : 16 ≤ L.P) {R : Region} (hR : Region.Disjoint R L.STK) (hS : Region.Disjoint R L.SCR) :
    Apart L.Q L.scr R where
  dF := by
    have hf := DLay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact hR.sub_right hf
  dS := hS.sub_right hL.ours_scr
  dK := hR.sub_right (sub_trans (DLay.Ok.ret_low (L := L) hP) DLay.Ok.low_stk)

/-- Where `out` and `*msg_len` are. -/
theorem outAt (hP : 16 ≤ L.P) {W : Nat → BitVec 64} (hS : Slots L W) :
    OutAt t L.Q L.scr W L.out L.ml L.k.toNat where
  ho := hS.out
  hml := hS.ml
  hw := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.OUT, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  hwm := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨L.ML, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  hnw := hL.bO
  ha := apart hL hP hL.kO.symm hL.oS
  ham := apart hL hP hL.kM.symm hL.mS
  hom := hL.oM

end Ctx

end VG.Proof.RsaOaep.AArch64.Dec
