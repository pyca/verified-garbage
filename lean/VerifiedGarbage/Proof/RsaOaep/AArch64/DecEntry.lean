module

public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay

/-! ### `RsaOaep.AArch64.DecLay`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on AArch64: where everything is

As for RSAES-PKCS1-v1_5 (`Proof/RsaPkcs1Enc/AArch64/DecLay.lean`): the
function's buffers and its stack, from the inner frame's base `Q` (`DLay`):
below it the `P` bytes the calls use (`LOW`), from it the inner frame (`FR`),
the frame holding our return address (`LR`, from `Q + 272`) and our stack
arguments (`ARGS`, from `Q + 288`), and MGF1's table (`TAB`). `DLay.Ok` is what the shared contract
says of them. `Ctx` is what holds between the frames' pushes and pops: the
frame's words are followed by the pieces' own `Rep`, and every piece's
`Step` keeps `Ctx` (`Ctx.step`). From `Ctx` and the slots, the pieces'
`Lay`, `LabAt` and `OutAt` (`Ctx.lay`, `Ctx.labAt`, `Ctx.outAt`).
-/

@[expose] public section

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
  tab : Addr
  tabL : Addr
  /-- The buffers read beyond those (`pre`, given the key's precomputed
  values), and the bytes `al` of our stack arguments. -/
  X : List Region
  al : Nat
  /-- The key's precomputed values and their length in words, given them. -/
  pre : Addr
  prl : BitVec 64
  /-- What the contract lets the function leak beyond `n` and `e`. -/
  lk : Mem → List Nat

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
abbrev ARGS : Region := ⟨L.Q + BitVec.ofNat 64 288, L.al⟩
/-- MGF1's table: its five words. -/
abbrev TAB : Region := Sig.tableRegion 64 L.tab 11
/-- The table of the label's hash function: its five words. -/
abbrev TABL : Region := Sig.tableRegion 64 L.tabL 11
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
  /-- And the tables. -/
  oT : L.OUT.Disjoint L.TAB
  mT : L.ML.Disjoint L.TAB
  sT : L.SCR.Disjoint L.TAB
  oTL : L.OUT.Disjoint L.TABL
  mTL : L.ML.Disjoint L.TABL
  sTL : L.SCR.Disjoint L.TABL
  /-- The stack misses every buffer. -/
  kO : L.STK.Disjoint L.OUT
  kM : L.STK.Disjoint L.ML
  kS : L.STK.Disjoint L.SCR
  kR : ∀ R ∈ L.ro, L.STK.Disjoint R
  kT : L.STK.Disjoint L.TAB
  kTL : L.STK.Disjoint L.TABL
  /-- No buffer wraps. -/
  bO : L.out.toNat + L.k.toNat ≤ 2 ^ 64
  bM : L.ml.toNat + 8 ≤ 2 ^ 64
  bS : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  bR : ∀ R ∈ L.ro, R.base.toNat + R.len ≤ 2 ^ 64
  bT : L.tab.toNat + 88 ≤ 2 ^ 64
  bTL : L.tabL.toNat + 88 ≤ 2 ^ 64
  nQ : L.Q.toNat + 424 ≤ 2 ^ 64
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
  /-- Our stack arguments, and the buffers read beyond the others. -/
  al136 : 136 ≤ L.al
  al152 : L.al ≤ 152
  nQa : L.Q.toNat + 288 + L.al ≤ 2 ^ 64
  xO : ∀ R ∈ L.X, R.Disjoint L.OUT
  xM : ∀ R ∈ L.X, R.Disjoint L.ML
  xS : ∀ R ∈ L.X, R.Disjoint L.SCR
  xK : ∀ R ∈ L.X, L.STK.Disjoint R
  xw : ∀ R ∈ L.X, R.base.toNat + R.len ≤ 2 ^ 64

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
  have := h.slk; unfold Spec.RsaPss.scratchWords at this; omega_using [this]

omit h in
/-- A range in our stack is in `STK`. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ 288) : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [q_add L.Q L.P d]; exact Offset.sub_base _ (by omega_using [hd])

omit h in
theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega_using [])

/-- A range in our frames misses the stack the calls use. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 424) : Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by have := h.nQ; have := h.pQ; omega_arith)

/-- Two ranges in our frames and arguments, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 424) (h₂ : d' + n' ≤ 424) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ ⟨L.Q + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ hs (by have := h.nQ; omega_using [h₁]) (by have := h.nQ; omega_using [h₂])

/-- A range in our frames misses the writable buffers. -/
theorem stk_buf {d n : Nat} (hd : d + n ≤ 288) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs := sub_stk (L := L) hd
  rcases hR with hR | hR | hR
  · exact (h.kO.sub_left hs).sub_right hR
  · exact (h.kM.sub_left hs).sub_right hR
  · exact (h.kS.sub_left hs).sub_right hR

/-- A range in our stack arguments misses the writable buffers. -/
theorem args_buf {d n : Nat} (h₁ : 288 ≤ d) (h₂ : d + n ≤ 424) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by have := h.al136; omega_using [h₂, this])
  rcases hR with hR | hR | hR
  · exact (h.oA.symm.sub_left hs).sub_right hR
  · exact (h.mA.symm.sub_left hs).sub_right hR
  · exact (h.sA.symm.sub_left hs).sub_right hR

/-- Our part of `scratch`. -/
theorem ours_scr : Region.Sub ⟨L.scr, oRsa⟩ L.SCR := Region.sub_prefix (by have := h.s8192; unfold oRsa; omega_using [this])

omit h in
/-- The 16 bytes below the frame, where the hash functions save their
return address, in the stack the calls use. -/
theorem ret_low (hP : 16 ≤ L.P) : Region.Sub (retR L.Q) L.LOW := Offset.sub_below _ hP (by omega_using [hP])

/-- The pieces' geometry. -/
theorem geo (hP : 16 ≤ L.P) : Geo L.Q L.scr where
  F16 := by have := h.pQ; omega_using [hP, this]
  Fw := by have := h.nQ; unfold frameBytes; omega_using [this]
  Sw := by have := h.bS; have := h.s8192; unfold oRsa; omega_arith
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
  | 8 => L.qil | 9 => L.lab | 10 => L.labl | 11 => L.ct | 12 => L.cl | 13 => L.scr | 14 => L.sl | 15 => L.tabL
  | _ => L.tab

/-- The state between the slots' writes and the frames' pops: `g` and `vv`
are the registers on entry, `m₀` the memory. -/
structure Ctx (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.PP, L.QQ, L.DP, L.DQ, L.QI, L.LAB, L.CT] ++ L.X ++ [L.TABL, L.TAB, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.ML, L.SCR]
  sp : t.sp = L.Q
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  lr : t.mem.readW (L.Q + BitVec.ofNat 64 272) 64 = g .x30
  args : ∀ j < 17, t.mem.readW (L.Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = ourArg L j
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
    (hd : 272 ≤ d) (hd₂ : d + 8 ≤ 288 ∨ 288 ≤ d) (hd' : d + 8 ≤ 424) :
    ∀ r ∈ ⟨L.Q, frameBytes⟩ :: ⟨L.scr, oRsa⟩ :: retR L.Q :: ws, Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ r := by
  have hb : ∀ R, InW L R → Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun R hR =>
    hd₂.elim (fun h₁ => hL.stk_buf h₁ hR) fun h₁ => hL.args_buf h₁ hd' hR
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · have := hL.fr_sep (d := d) (n := 8) (d' := 0) (n' := frameBytes) (by unfold frameBytes; omega_using [hd]) hd'
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
  have hk : ∀ d, 272 ≤ d → (d + 8 ≤ 288 ∨ 288 ≤ d) → d + 8 ≤ 424 →
      t'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ h₃ => hS.frame.readW (Region.contains_self _ _) (kept_apart hL hP hws h₁ h₂ h₃) (by decide)
  refine ⟨hS.rd.trans hc.rd, hS.wr.trans hc.wr, hS.sp.trans hc.sp,
    fun r hr h30 => (hS.cs r hr h30).trans (hc.cs r hr h30), fun r hr => (hS.vec r hr).trans (hc.vs r hr),
    (hk 272 (by decide) (by decide) (by decide)).trans hc.lr,
    fun j hj => (hk _ (by omega_using []) (by omega_using []) (by omega_using [hj])).trans (hc.args j hj), hc.frame.trans (hS.frame.sub fun r hr => ?_)⟩
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
      have := hL.s8192; show 0 + oRsa ≤ L.sl.toNat * 8; unfold oRsa; omega_using [this]⟩
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

/-- MGF1's table, at the stack argument 16, from what the entry's memory
holds there: the table and that argument are apart from everything the
function writes. -/
theorem tab (hP : 16 ≤ L.P) {G : Impl.Pbkdf2.Md.AArch64.Stream} {f : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}
    (ok : Table.TabOK G f t.syms) (hm : Table.TabMem G t.syms L.tab m₀)
    (hD : m₀.readW (L.tab + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 G.D) :
    Table.Tab G f L.Q L.scr L.tab (arg 16) t := by
  have cT : ∀ d, d + 8 ≤ 88 → L.TAB.Contains (L.tab + BitVec.ofNat 64 d) 8 := fun d hd => by
    show (⟨L.tab, 88⟩ : Region).Contains _ _
    exact Offset.contains_base _ hd (by omega_using [hd])
  have cA : L.ARGS.Contains (L.Q + BitVec.ofNat 64 (arg 16)) 8 :=
    Offset.contains _ (by decide) (by have := hL.al136; unfold arg frameBytes; omega_using [this])
      (by have := hL.al152; omega_using [this])
  have mT : L.TAB ∈ t.rd ++ t.wr := List.mem_append_left _ (by rw [hc.rd]; simp)
  have mA : L.ARGS ∈ t.rd ++ t.wr := List.mem_append_left _ (by rw [hc.rd]; simp)
  have dT : ∀ r ∈ Table.mgfRs L.Q L.scr, L.TAB.Disjoint r := by
    intro r hr
    simp only [Table.mgfRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hf := DLay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
      rw [BitVec.add_zero] at hf
      exact hL.kT.symm.sub_right hf
    · exact hL.sT.symm.sub_right hL.ours_scr
    · exact hL.kT.symm.sub_right (sub_trans (DLay.Ok.ret_low (L := L) hP) DLay.Ok.low_stk)
  have dT0 : ∀ r ∈ [L.OUT, L.ML, L.SCR, L.STK], L.TAB.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.oT.symm
    · exact hL.mT.symm
    · exact hL.sT.symm
    · exact hL.kT.symm
  refine ⟨ok, fun j hj => ⟨_, mT, cT _ (by omega_using [hj])⟩, ⟨_, mT, cT 48 (by decide)⟩, ⟨_, mA, cA⟩, fun m hf => ?_⟩
  have rt : ∀ d, d + 8 ≤ 88 → m.readW (L.tab + BitVec.ofNat 64 d) 64 = m₀.readW (L.tab + BitVec.ofNat 64 d) 64 :=
    fun d hd => (hf.readW (cT d hd) dT (by decide)).trans (hc.frame.readW (cT d hd) dT0 (by decide))
  refine ⟨⟨(rt _ (by decide)).trans hm.1, (rt _ (by decide)).trans hm.2.1, (rt _ (by decide)).trans hm.2.2⟩,
    (rt 48 (by decide)).trans hD, ?_⟩
  have ka := kept_apart hL hP (ws := []) (fun _ h => absurd h List.not_mem_nil) (d := 416) (by decide)
    (by decide) (by decide)
  show m.readW (L.Q + BitVec.ofNat 64 (288 + 8 * 16)) 64 = L.tab
  exact (hf.readW (Region.contains_self _ _) ka (by decide)).trans (hc.args 16 (by decide))


/-- The table of the label's hash function, at the stack argument 15, from what the entry's memory
holds there: the table and that argument are apart from everything the
function writes. -/
theorem tabL (hP : 16 ≤ L.P) {G : Impl.Pbkdf2.Md.AArch64.Stream} {f : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}
    (ok : Table.TabOK G f t.syms) (hm : Table.TabMem G t.syms L.tabL m₀)
    (hD : m₀.readW (L.tabL + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 G.D) :
    Table.Tab G f L.Q L.scr L.tabL (arg 15) t := by
  have cT : ∀ d, d + 8 ≤ 88 → L.TABL.Contains (L.tabL + BitVec.ofNat 64 d) 8 := fun d hd => by
    show (⟨L.tabL, 88⟩ : Region).Contains _ _
    exact Offset.contains_base _ hd (by omega_using [hd])
  have cA : L.ARGS.Contains (L.Q + BitVec.ofNat 64 (arg 15)) 8 :=
    Offset.contains _ (by decide) (by have := hL.al136; unfold arg frameBytes; omega_using [this])
      (by have := hL.al152; omega_using [this])
  have mT : L.TABL ∈ t.rd ++ t.wr := List.mem_append_left _ (by rw [hc.rd]; simp)
  have mA : L.ARGS ∈ t.rd ++ t.wr := List.mem_append_left _ (by rw [hc.rd]; simp)
  have dT : ∀ r ∈ Table.mgfRs L.Q L.scr, L.TABL.Disjoint r := by
    intro r hr
    simp only [Table.mgfRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hf := DLay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
      rw [BitVec.add_zero] at hf
      exact hL.kTL.symm.sub_right hf
    · exact hL.sTL.symm.sub_right hL.ours_scr
    · exact hL.kTL.symm.sub_right (sub_trans (DLay.Ok.ret_low (L := L) hP) DLay.Ok.low_stk)
  have dT0 : ∀ r ∈ [L.OUT, L.ML, L.SCR, L.STK], L.TABL.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.oTL.symm
    · exact hL.mTL.symm
    · exact hL.sTL.symm
    · exact hL.kTL.symm
  refine ⟨ok, fun j hj => ⟨_, mT, cT _ (by omega_using [hj])⟩, ⟨_, mT, cT 48 (by decide)⟩, ⟨_, mA, cA⟩, fun m hf => ?_⟩
  have rt : ∀ d, d + 8 ≤ 88 → m.readW (L.tabL + BitVec.ofNat 64 d) 64 = m₀.readW (L.tabL + BitVec.ofNat 64 d) 64 :=
    fun d hd => (hf.readW (cT d hd) dT (by decide)).trans (hc.frame.readW (cT d hd) dT0 (by decide))
  refine ⟨⟨(rt _ (by decide)).trans hm.1, (rt _ (by decide)).trans hm.2.1, (rt _ (by decide)).trans hm.2.2⟩,
    (rt 48 (by decide)).trans hD, ?_⟩
  have ka := kept_apart hL hP (ws := []) (fun _ h => absurd h List.not_mem_nil) (d := 408) (by decide)
    (by decide) (by decide)
  show m.readW (L.Q + BitVec.ofNat 64 (288 + 8 * 15)) 64 = L.tabL
  exact (hf.readW (Region.contains_self _ _) ka (by decide)).trans (hc.args 15 (by decide))

end Ctx

end VG.Proof.RsaOaep.AArch64.Dec

end

end

/-!
# RSAES-OAEP decryption on AArch64: entering the frames

As for RSAES-PKCS1-v1_5 (`Proof/RsaPkcs1Enc/AArch64/DecEntry.lean`): the
layout of a call (`lay`), what the shared contract says of it (`lay_ok`),
and the prologue (`prologue_ok`), run from the state in which the inner
frame's body starts (`entered`): it saves our register arguments to their
slots (`Spill.save_wp`) and moves our stack arguments to theirs and to the
private-key operation's (`moves_ok`), establishing `Ctx`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (q_add add_add read8 write8 toNat_sub_k preserved_ne)

/-- The shared contract, with both hash functions each one of the tables
`ts` and `P + 288` bytes of stack. -/
abbrev decSpec (ts : List FnTable) (P : Nat) : Contract isa :=
  Spec.RsaOaep.decryptMdTablesContract (AArch64.abi.withTables Spec.RsaOaep.decryptMdTablesSig
    [("hash", ts), ("mgf1", ts)]) (P + 288)

/-- Unfolds the contract's precondition at `h`. -/
macro "dec_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at $h:ident
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- What a layout has beyond the shared contract's arguments: the buffers
read beyond those, the bytes of our stack arguments, the key's precomputed
values and what the contract lets the function leak beyond `n` and `e`;
none for the shared contract. -/
structure DX where
  X : List Region := []
  al : Nat := 136
  pre : Addr := 0
  prl : BitVec 64 := 0
  lk : Mem → List Nat := fun _ => []

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
def lay (P : Nat) (s : State) (x : DX := {}) : DLay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13,
    stackArg s 14, s.sp - BitVec.ofNat 64 288, P, stackArg s 16, stackArg s 15, x.X, x.al, x.pre, x.prl, x.lk⟩

theorem lay_Q (P : Nat) (s : State) (x : DX := {}) : (lay P s x).Q + BitVec.ofNat 64 288 = s.sp :=
  BitVec.sub_add_cancel _ _

theorem lay_args (P : Nat) (s : State) (x : DX := {}) :
    (lay P s x).Q + BitVec.ofNat 64 288 = stackArgAddr s 0 := by
  rw [lay_Q P s x, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (P : Nat) (s : State) (x : DX := {}) :
    (lay P s x).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 288) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, Nat.add_comm 288 P]

theorem forall_ro {L : DLay} {F : Region → Prop}
    (h : F L.N ∧ F L.E ∧ F L.PP ∧ F L.QQ ∧ F L.DP ∧ F L.DQ ∧ F L.QI ∧ F L.LAB ∧ F L.CT) : ∀ R ∈ L.ro, F R := by
  intro R hR
  simp only [DLay.ro, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem nil_x {F : Region → Prop} : ∀ R ∈ ([] : List Region), F R := fun _ h => absurd h List.not_mem_nil

theorem lay_ok {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s) :
    (lay P s).Ok := by
  dec_pre at h
  sig_split h
  rename_i hsp hsp2 hheld hheld2 hpw hdrop1 hdrop2 oM oN oE oP oQ oDP oDQ oQI oL oC oS oTL oT oA mN mE mP mQ mDP
    mDQ mQI mL mC mS mTL mT mA nS eS pS qS dpS dqS qiS lS cS sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC kS kTL kT
    hdrop3 bO bM bN bE bP bQ bDP bDQ bQI bL bC bS bTL bT kv hk1 hk2 el1 elk pl1 plk ql1 qlk hdp hqi hdq
  clear hdrop1 hdrop2 hdrop3 hheld hheld2 hpw
  have slk := h
  clear h
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oP oQ oDP oDQ oQI oL oC oS oM oT oTL mC mDP mDQ mQI cS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kC kDP kDQ kQI bO bC bDP bDQ bQI
  obtain eA : (lay P s).ARGS = ⟨stackArgAddr s 0, 136⟩ := by
    show (⟨(lay P s).Q + BitVec.ofNat 64 288, 136⟩ : Region) = _
    rw [lay_args]
  obtain eK : (lay P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 288), P + 288⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region) = _
    rw [lay_stk]
  obtain hQ : (lay P s).Q.toNat = s.sp.toNat - 288 := toNat_sub_k (by omega_arith)
  refine ⟨oM, oS, mS, forall_ro ⟨oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC⟩,
    forall_ro ⟨mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC⟩,
    forall_ro ⟨nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm⟩, eA ▸ oA,
    eA ▸ mA, eA ▸ sA, oT, mT, sT, oTL, mTL, sTL, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kP,
    eK ▸ kQ, eK ▸ kDP, eK ▸ kDQ, eK ▸ kQI, eK ▸ kL, eK ▸ kC⟩, eK ▸ kT, eK ▸ kTL, bO, bM, bS,
    forall_ro ⟨bN, bE, bP, bQ, bDP, bDQ, bQI, bL, bC⟩, bT, bTL,
    by omega_arith, by simp only [lay] at hQ ⊢; omega_arith, kv, hk1, hk2, el1, elk, pl1, plk, ql1, qlk, hdp, hqi, hdq, slk,
    Nat.le_refl _, (by decide : 136 ≤ 152), by show _ + 288 + 136 ≤ _; omega_arith, nil_x, nil_x, nil_x, nil_x, nil_x⟩

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 15 and MGF1's at 16, with the
functions of distinct names at distinct addresses. -/
theorem spec_tab {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (·.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  dec_pre at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.sublist (List.sublist_append_left _ _)⟩

/-! ## Moving the stack arguments -/

/-- The memory after moving the word at `B + arg j` (as in `m₀`) to `B + d`
for each `(j, d)`, in order. -/
def moveMem (m : Mem) (B : Addr) (m₀ : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (j, d) :: l => moveMem (m.writeW (B + BitVec.ofNat 64 d) (m₀.readW (B + BitVec.ofNat 64 (arg j)) 64)) B m₀ l

/-- The moves' destinations are words of the frame, and their sources our
stack arguments. -/
def MoveOk (l : List (Nat × Nat)) : Prop := ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 + 8 ≤ frameBytes ∧ p.1 < 15

instance (l : List (Nat × Nat)) : Decidable (MoveOk l) := by unfold MoveOk; infer_instance

theorem moveMem_frame {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) :
    Frame [⟨B, frameBytes⟩] m (moveMem m B m₀ l) := by
  suffices h : ∀ m', Frame [⟨B, frameBytes⟩] m m' → Frame [⟨B, frameBytes⟩] m (moveMem m' B m₀ l) from
    h m (Frame.refl _ _)
  induction l with
  | nil => exact fun _ h => h
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro m' h
    obtain hd := hl (j, d) List.mem_cons_self
    have hd2 : d + 8 ≤ 272 := hd.2.1
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      (h.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold frameBytes; omega_arith) (by omega_arith)))

theorem moveMem_read {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) {a : Nat}
    (ha : ∀ p ∈ l, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2) (ha' : a + 8 ≤ 424) :
    (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 a) 64 = m.readW (B + BitVec.ofNat 64 a) 64 := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    obtain hd := hl (j, d) List.mem_cons_self
    rw [moveMem, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ (fun q hq => ha q (List.mem_cons_of_mem _ hq)),
      Mem.readW_writeW_sep (Offset.sep _ (by have := ha (j, d) List.mem_cons_self; dsimp only at this; omega_arith)
        (by omega_arith) (by unfold frameBytes at hd; omega_arith)) (by decide)]

theorem moveMem_moved {l : List (Nat × Nat)} (hl : MoveOk l) (hn : (l.map Prod.snd).Nodup) {B : Addr}
    (m m₀ : Mem) :
    ∀ p ∈ l, (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 p.2) 64 = m₀.readW (B + BitVec.ofNat 64 (arg p.1)) 64 := by
  induction l generalizing m with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hd := hl (j, d) List.mem_cons_self
      obtain hne : ∀ q ∈ l, q.2 ≠ d := fun q hq e =>
        (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨q, hq, e⟩)
      rw [moveMem, moveMem_read (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ (fun q hq => by
        have := hl q (List.mem_cons_of_mem _ hq); have := hne q hq
        obtain h8 : q.2 % 8 = 0 := (hl q (List.mem_cons_of_mem _ hq)).1
        have h8' : d % 8 = 0 := hd.1
        omega_arith) (by unfold frameBytes at hd; dsimp only; omega_arith), Mem.readW_writeW_self64]
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hn).2 _ q hq

/-- After the moves, from `t`. -/
structure Moved (t u : State) (l : List (Nat × Nat)) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = moveMem t.mem t.sp t.mem l
  other : ∀ r, r ≠ .x10 → u.gpr r = t.gpr r

/-- One move. -/
theorem mv_step {u : State} {j d : Nat} (ho : arg j % 8 = 0 ∧ arg j < 32768) (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (arg j)) 8)
    (hw : InRegions u.wr (u.gpr .x9 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (mvArg j d)) u fun u₁ => u₁.rd = u.rd ∧ u₁.wr = u.wr ∧ u₁.sp = u.sp ∧ u₁.v = u.v ∧
      u₁.mem = u.mem.writeW (u.gpr .x9 + BitVec.ofNat 64 d) (u.mem.readW (u.sp + BitVec.ofNat 64 (arg j)) 64) ∧
      ∀ r, r ≠ .x10 → u₁.gpr r = u.gpr r := by
  apply WP.of_runBlock
  rw [mvArg, runBlock_cons, Bytes.exec_ldrSp ho hr, runStep_some, runBlock_cons,
    exec_str_x hd (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact hw),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩
  show (u.mem.writeW _ _) = _
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]

theorem moves_ok {l : List (Nat × Nat)} (hl : MoveOk l) {t : State} (h9 : t.gpr .x9 = t.sp)
    (hw : ∀ p ∈ l, InRegions t.wr (t.sp + BitVec.ofNat 64 p.2) 8)
    (hr : ∀ p ∈ l, InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) :
    WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) t fun u => Moved t u l := by
  suffices h : ∀ (l : List (Nat × Nat)), MoveOk l → ∀ (u : State), u.gpr .x9 = t.sp → u.sp = t.sp →
      u.rd = t.rd → u.wr = t.wr →
      (∀ p ∈ l, u.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64 = t.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64) →
      (∀ p ∈ l, InRegions u.wr (t.sp + BitVec.ofNat 64 p.2) 8) →
      (∀ p ∈ l, InRegions (u.rd ++ u.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) →
      WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        u'.sp = u.sp ∧ u'.v = u.v ∧ u'.mem = moveMem u.mem t.sp t.mem l ∧ ∀ r, r ≠ .x10 → u'.gpr r = u.gpr r by
    exact WP.mono (h l hl t h9 rfl rfl rfl (fun _ _ => rfl) hw hr) fun u ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩
  intro l
  induction l with
  | nil => exact fun _ u _ _ _ _ _ _ _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro hl u h9 hsp hrd hwr hsrc hw hr
    obtain hd := hl (j, d) List.mem_cons_self
    obtain hw₀ := hw (j, d) List.mem_cons_self
    obtain hr₀ := hr (j, d) List.mem_cons_self
    obtain hs₀ := hsrc (j, d) List.mem_cons_self
    dsimp only at hd hw₀ hr₀ hs₀
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ho : arg j % 8 = 0 ∧ arg j < 32768 := by unfold arg frameBytes; omega_arith
    obtain hd' : d % 8 = 0 ∧ d < 32768 := ⟨hd.1, by unfold frameBytes at hd; omega_arith⟩
    refine WP.mono (mv_step ho hd' (by rw [hsp]; exact hr₀) (by rw [h9]; exact hw₀))
      fun u₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
    obtain e₁ : ∀ a, a < 15 → u₁.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 =
        u.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 := fun a ha => by
      rw [m₁, h9]
      exact Mem.readW_writeW_sep (Offset.sep _ (by unfold arg frameBytes at *; omega_arith)
        (by unfold arg frameBytes; omega_arith) (by unfold frameBytes at hd; omega_arith)) (by decide)
    refine WP.mono (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) u₁
      (by rw [g₁ .x9 (by decide), h9]) (s₁.trans hsp) (r₁.trans hrd) (w₁.trans hwr)
      (fun q hq => (e₁ q.1 (hl q (List.mem_cons_of_mem _ hq)).2.2).trans (hsrc q (List.mem_cons_of_mem _ hq)))
      (fun q hq => by rw [w₁]; exact hw q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [r₁, w₁]; exact hr q (List.mem_cons_of_mem _ hq)))
      fun u' ⟨a, b, c, e, f, g⟩ => ⟨a.trans r₁, b.trans w₁, c.trans s₁, e.trans v₁, ?_, fun r hr =>
        (g r hr).trans (g₁ r hr)⟩
    rw [f, m₁, moveMem, h9, hsp, hs₀]

/-! ## The prologue -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (P : Nat) (s : State) (x : DX := {}) : (entered s).sp = (lay P s x).Q := by
  show s.sp - 16 - BitVec.ofNat 64 272 = s.sp - BitVec.ofNat 64 288
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (P : Nat) (s : State) (x : DX := {}) : s.sp - 16 = (lay P s x).Q + BitVec.ofNat 64 272 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 288 + BitVec.ofNat 64 272
  bv_omega

theorem entered_wr (P : Nat) (s : State) (x : DX := {}) :
    (entered s).wr = (lay P s x).FR :: (lay P s x).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 272, 272⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 272 = (lay P s x).Q from entered_sp P s x, lr_slot P s x]
  rfl

theorem entered_mem (P : Nat) (s : State) (x : DX := {}) :
    (entered s).mem = s.mem.writeW ((lay P s x).Q + BitVec.ofNat 64 272) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot P s x, write8]

theorem ourArg_lay (P : Nat) (s : State) (x : DX := {}) : ∀ j, j < 17 → ourArg (lay P s x) j = stackArg s j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl | 15, _ => rfl | 16, _ => rfl | _ + 17, h => absurd h (by omega_using [])

/-- The register arguments' slots. -/
abbrev saveList : List (Reg × Nat) := [(.x0, sOut), (.x2, sMl), (.x3, sN), (.x4, sK), (.x5, sE), (.x6, sEl), (.x7, 0)]

/-- The stack arguments' moves: the label, its length and `scratch` to
their slots, and ours from `p_len` to `qinv_len` to the frame's words 1 to
9. -/
def argMoves : List (Nat × Nat) :=
  [(9, sLab), (10, sLabLen), (13, sScr), (14, sScrLen)] ++ (List.range 9).map fun j => (j, 8 * (j + 1))

theorem decPrologue_eq : decPrologue = ([.addSp .x9 0] : List Instr) ++ Spill.saveCode .x9 saveList ++
    argMoves.flatMap (fun p => mvArg p.1 p.2) := rfl

theorem argMoves_ok : MoveOk argMoves := by decide

theorem argMoves_nodup : (argMoves.map Prod.snd).Nodup := by decide

theorem mem_argMoves {j : Nat} (hj : j < 9) : (j, 8 * (j + 1)) ∈ argMoves :=
  List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The saves' slots are not the moves'. -/
theorem argMoves_apart {a : Nat} (ha : a ∈ saveList.map Prod.snd) :
    ∀ p ∈ argMoves, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2 := by
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The regions the contract grants. -/
theorem spec_rdwr {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s) :
    s.rd = [(lay P s).N, (lay P s).E, (lay P s).PP, (lay P s).QQ, (lay P s).DP, (lay P s).DQ, (lay P s).QI,
      (lay P s).LAB, (lay P s).CT] ++ (lay P s).X ++ [(lay P s).TABL, (lay P s).TAB, (lay P s).ARGS] ∧
      s.wr = [(lay P s).OUT, (lay P s).ML, (lay P s).SCR] := by
  obtain hL := lay_ok h
  dec_pre at h
  obtain ⟨-, -, -, -, -, hrd, hwr, -⟩ := h
  have hk1 : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
  have hk2 : (stackArg s 12).toNat = (s.gpr .x4).toNat := hL.clk
  have hdp : (stackArg s 4).toNat = (stackArg s 0).toNat := hL.dpl
  have hqi : (stackArg s 8).toNat = (stackArg s 0).toNat := hL.qil
  have hdq : (stackArg s 6).toNat = (stackArg s 2).toNat := hL.dql
  rw [hrd, hwr, hk1, hk2, hdp, hqi, hdq, ← lay_args P]
  exact ⟨rfl, rfl⟩

/-- The frame's words as the prologue leaves them. -/
structure Prologued (L : DLay) (W : Nat → BitVec 64) : Prop where
  slots : Slots L W
  p : W 0 = L.p
  args : ∀ j < 9, W (j + 1) = ourArg L j

/-- The prologue, for a layout whose regions are those `s` grants. -/
theorem prologueX_ok {P : Nat} {s : State} {x : DX} (hL : (lay P s x).Ok)
    (hrd : s.rd = [(lay P s x).N, (lay P s x).E, (lay P s x).PP, (lay P s x).QQ, (lay P s x).DP, (lay P s x).DQ,
      (lay P s x).QI, (lay P s x).LAB, (lay P s x).CT] ++ (lay P s x).X ++
      [(lay P s x).TABL, (lay P s x).TAB, (lay P s x).ARGS])
    (hwr : s.wr = [(lay P s x).OUT, (lay P s x).ML, (lay P s x).SCR]) :
    WP isa (.block decPrologue) (entered s) fun t => Ctx (lay P s x) s.gpr s.v s.mem t ∧
      t.gpr .x9 = (lay P s x).Q ∧ Prologued (lay P s x) (fun j => word t.mem (lay P s x).Q (8 * j)) := by
  have hnQ := hL.nQ
  have hpQ : P ≤ (lay P s x).Q.toNat := hL.pQ
  have hal := hL.al136
  have hal' := hL.al152
  obtain hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes →
      InRegions u.wr ((lay P s x).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay P s x).FR, by rw [hu, entered_wr P s x]; simp,
      Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)⟩
  obtain harg : ∀ (u : State) d, u.rd = s.rd → 288 ≤ d → d + 8 ≤ 424 →
      InRegions (u.rd ++ u.wr) ((lay P s x).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay P s x).ARGS, by rw [hu, hrd]; simp, Offset.contains _ h₁ (by omega_arith)
      (by have := hL.nQa; omega_arith)⟩
  obtain eLr : (entered s).mem.readW ((lay P s x).Q + BitVec.ofNat 64 272) 64 = s.gpr .x30 := by
    rw [entered_mem P s x, Mem.readW_writeW_self64]
  obtain eArg : ∀ j, j < 17 → (entered s).mem.readW ((lay P s x).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 =
      stackArg s j := by
    intro j hj
    rw [entered_mem P s x, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      stackArg, stackArgAddr, ← lay_Q P s x, add_add]
  obtain eFr : Frame [(lay P s x).STK] s.mem (entered s).mem := by
    rw [entered_mem P s x]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay P s x).Q - BitVec.ofNat 64 P, P + 288⟩ : Region).Contains
      ((lay P s x).Q + BitVec.ofNat 64 272) (64 / 8)
    rw [q_add (lay P s x).Q P 272]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [decPrologue_eq, List.append_assoc, WP.block_append_iff]
  -- `x9 = sp`.
  obtain h0 : WP isa (.block [.addSp .x9 0]) (entered s) fun t₀ => t₀ = (entered s).write .x .x9 (lay P s x).Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, entered_sp P s x,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  obtain h9 : ((entered s).write .x .x9 (lay P s x).Q).gpr .x9 = (lay P s x).Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) (fun p hp => ?_)) fun t₂ hs => ?_
  · rw [h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr _ _ _ (RegUpd.wr_write ..) (by decide)
  obtain hsp₂ : t₂.sp = (lay P s x).Q := hs.sp.trans ((RegUpd.sp_write ..).trans (entered_sp P s x))
  obtain hrd₂ : t₂.rd = s.rd := hs.rd.trans (RegUpd.rd_write ..)
  obtain hwr₂ : t₂.wr = (entered s).wr := hs.wr.trans (RegUpd.wr_write ..)
  refine WP.mono (moves_ok argMoves_ok (t := t₂) (by rw [hs.gpr, h9, hsp₂])
    (fun p hp => by rw [hsp₂]; exact hfr _ _ _ hwr₂ (argMoves_ok p hp).2.1)
    (fun p hp => by
      have := (argMoves_ok p hp).2.2
      rw [hsp₂]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega_arith) (by unfold arg frameBytes; omega_arith)))
    fun u hm => ?_
  -- The memory.
  obtain M2 : t₂.mem = Spill.saveMem (entered s).mem (lay P s x).Q ((entered s).write .x .x9 (lay P s x).Q).gpr
      saveList := by
    rw [hs.mem, h9, RegUpd.mem_write]
  obtain F2 : Frame [⟨(lay P s x).Q, 224⟩] (entered s).mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  obtain S2 : Spill.Saved (lay P s x).Q ((entered s).write .x .x9 (lay P s x).Q).gpr saveList t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain U : u.mem = moveMem t₂.mem (lay P s x).Q t₂.mem argMoves := by rw [hm.mem, hsp₂]
  obtain hi₂ : ∀ d, 224 ≤ d → d + 8 ≤ 424 → t₂.mem.readW ((lay P s x).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s x).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  -- Our stack arguments, unchanged.
  obtain uArg : ∀ j, j < 17 → u.mem.readW ((lay P s x).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [U, moveMem_read argMoves_ok _ _ (fun p hp => by
      have := (argMoves_ok p hp).2.1; unfold frameBytes at this; omega_arith) (by omega_arith),
      hi₂ _ (by omega_arith) (by omega_arith), eArg j hj]
  obtain uMv : ∀ p ∈ argMoves, u.mem.readW ((lay P s x).Q + BitVec.ofNat 64 p.2) 64 = stackArg s p.1 := by
    intro p hp
    have := (argMoves_ok p hp).2.2
    rw [U, moveMem_moved argMoves_ok argMoves_nodup _ _ p hp, show arg p.1 = 288 + 8 * p.1 from rfl,
      hi₂ _ (by omega_arith) (by omega_arith), eArg _ (by omega_using [this])]
  obtain uSv : ∀ r d, (r, d) ∈ saveList → u.mem.readW ((lay P s x).Q + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hrd
    rw [U, moveMem_read argMoves_ok _ _ (argMoves_apart (List.mem_map_of_mem (f := Prod.snd) hrd))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
          rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> (dsimp only; decide)),
      S2 (r, d) hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
    rcases hrd with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact RegUpd.gpr_write_of_ne _ _ _ (by dsimp only; decide)
  obtain F : Frame [⟨(lay P s x).Q, 272⟩] (entered s).mem u.mem := by
    rw [U]
    refine Frame.trans (F2.sub fun r hr => ?_) ((moveMem_frame argMoves_ok _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold frameBytes; omega_arith)⟩
  obtain go : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [hm.other r h₂, hs.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ h₁
  obtain w8 : ∀ d, word u.mem (lay P s x).Q d = u.mem.readW ((lay P s x).Q + BitVec.ofNat 64 d) 64 := fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hm.rd, hrd₂, hrd]
  · rw [hm.wr, hwr₂, entered_wr P s x, hwr]
  · rw [hm.sp, hsp₂]
  · intro r hr _
    exact go r (preserved_ne hr (by decide)) (preserved_ne hr (by decide))
  · intro r _
    rw [hm.v, hs.v, RegUpd.v_write, entered_v]
  · rw [U, moveMem_read argMoves_ok _ _ (by decide) (by omega_arith), hi₂ 272 (by omega_arith) (by omega_arith), eLr]
  · intro j hj
    rw [uArg j hj, ourArg_lay P s x j hj]
  · have hk : (lay P s x).STK ∈ [(lay P s x).OUT, (lay P s x).ML, (lay P s x).SCR, (lay P s x).STK] := by simp
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    obtain h272 := DLay.Ok.sub_stk (L := lay P s x) (d := 0) (n := 272) (by omega_arith)
    rw [show (lay P s x).Q + BitVec.ofNat 64 0 = (lay P s x).Q from BitVec.add_zero _] at h272
    exact ⟨(lay P s x).STK, hk, h272⟩
  · rw [hm.other .x9 (by decide), hs.gpr, h9]
  · rw [w8]; exact uMv (13, sScr) (by decide)
  · rw [w8]; exact uSv .x0 sOut (by simp)
  · rw [w8]; exact uSv .x3 sN (by simp)
  · rw [w8]; exact uSv .x4 sK (by simp)
  · rw [w8]; exact uSv .x5 sE (by simp)
  · rw [w8]; exact uSv .x6 sEl (by simp)
  · rw [w8]; exact uMv (14, sScrLen) (by decide)
  · rw [w8]; exact uMv (9, sLab) (by decide)
  · rw [w8]; exact uMv (10, sLabLen) (by decide)
  · rw [w8]; exact uSv .x2 sMl (by simp)
  · rw [w8]; exact uSv .x7 0 (by simp)
  · intro j hj
    rw [w8, uMv _ (mem_argMoves hj), ourArg_lay P s x j (by omega_arith)]

theorem prologue_ok {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s) :
    WP isa (.block decPrologue) (entered s) fun t => Ctx (lay P s) s.gpr s.v s.mem t ∧
      t.gpr .x9 = (lay P s).Q ∧ Prologued (lay P s) (fun j => word t.mem (lay P s).Q (8 * j)) :=
  prologueX_ok (lay_ok h) (spec_rdwr h).1 (spec_rdwr h).2

end VG.Proof.RsaOaep.AArch64.Dec
