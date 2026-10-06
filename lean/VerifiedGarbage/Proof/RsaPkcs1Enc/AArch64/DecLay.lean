import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Decrypt
import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: where everything is

The function's buffers and its stack, from the inner frame's base `Q`
(`Lay`): below it the `P` bytes the calls use (`LOW`), from it the inner
frame (`FR`: the private-key operation's stack arguments, then the slots),
the frame holding our return address (`LR`, from `Q + 208`) and our stack
arguments (`ARGS`, from `Q + 224`). `lay_ok` reads what the shared contract
says of them (`Lay.Ok`). `Ctx` is what holds between the frames' pushes and
pops once the slots are written, and `Kept` the words in the frames that
no step changes.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

/-- The arguments, the inner frame's base `Q` and the bytes `P` below it the
calls use. -/
structure Lay where
  out : Addr
  ol : BitVec 64
  ml : Addr
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  d : Addr
  dl : BitVec 64
  inp : Addr
  il : BitVec 64
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
  scr : Addr
  sl : BitVec 64
  Q : Addr
  P : Nat

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, L.k.toNat⟩
abbrev ML : Region := ⟨L.ml, 8⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev D : Region := ⟨L.d, L.dl.toNat⟩
abbrev INP : Region := ⟨L.inp, L.k.toNat⟩
abbrev PP : Region := ⟨L.p, L.pl.toNat⟩
abbrev QQ : Region := ⟨L.q, L.ql.toNat⟩
abbrev DP : Region := ⟨L.dp, L.pl.toNat⟩
abbrev DQ : Region := ⟨L.dq, L.ql.toNat⟩
abbrev QI : Region := ⟨L.qi, L.pl.toNat⟩
abbrev SCR : Region := ⟨L.scr, L.sl.toNat * 8⟩
abbrev FR : Region := ⟨L.Q, frameBytes⟩
abbrev LR : Region := ⟨L.Q + BitVec.ofNat 64 208, 16⟩
abbrev ARGS : Region := ⟨L.Q + BitVec.ofNat 64 224, 120⟩
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 224⟩

/-- The buffers the function only reads. -/
def ro : List Region := [L.N, L.E, L.D, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI]

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
  nQ : L.Q.toNat + 344 ≤ 2 ^ 64
  pQ : L.P ≤ L.Q.toNat
  /-- The lengths. -/
  kv : Spec.Rsa.lenValid L.k.toNat
  olk : L.ol.toNat = L.k.toNat
  ilk : L.il.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  dl1 : 1 ≤ L.dl.toNat
  dlk : L.dl.toNat ≤ L.k.toNat
  pl1 : 1 ≤ L.pl.toNat
  plk : L.pl.toNat < L.k.toNat
  ql1 : 1 ≤ L.ql.toNat
  qlk : L.ql.toNat < L.k.toNat
  dpl : L.dpl.toNat = L.pl.toNat
  qil : L.qil.toNat = L.pl.toNat
  dql : L.dql.toNat = L.ql.toNat
  slk : Spec.Rsa.scratchWords L.k.toNat ≤ L.sl.toNat

end Lay

/-! ## Offsets from `Q` -/

/-- A range within a writable buffer. -/
def InW (L : Lay) (R : Region) : Prop := Region.Sub R L.OUT ∨ Region.Sub R L.ML ∨ Region.Sub R L.SCR


namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem k64 : 64 ≤ L.k.toNat := h.kv.1
theorem k1024 : L.k.toNat ≤ 1024 := h.kv.2

/-- `scratch` holds 8192 bytes at least. -/
theorem s8192 : 8192 ≤ L.sl.toNat * 8 := by
  have := h.slk; have := h.k64; unfold Spec.Rsa.scratchWords at *; omega

omit h in
/-- A range in our stack is in `STK`. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ 224) : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [Enc.q_add L.Q L.P d]; exact Offset.sub_base _ (by omega)

omit h in
theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega)

/-- A range in our frames misses the stack the calls use. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 344) : Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by have := h.nQ; have := h.pQ; omega)

/-- Two ranges in our frames and arguments, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 344) (h₂ : d' + n' ≤ 344) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ ⟨L.Q + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ hs (by have := h.nQ; omega) (by have := h.nQ; omega)

/-- A range in our frames misses the writable buffers. -/
theorem stk_buf {d n : Nat} (hd : d + n ≤ 224) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs := Lay.Ok.sub_stk (L := L) hd
  rcases hR with hR | hR | hR
  · exact (h.kO.sub_left hs).sub_right hR
  · exact (h.kM.sub_left hs).sub_right hR
  · exact (h.kS.sub_left hs).sub_right hR

/-- A range in our stack arguments misses the writable buffers. -/
theorem args_buf {d n : Nat} (h₁ : 224 ≤ d) (h₂ : d + n ≤ 344) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  rcases hR with hR | hR | hR
  · exact (h.oA.symm.sub_left hs).sub_right hR
  · exact (h.mA.symm.sub_left hs).sub_right hR
  · exact (h.sA.symm.sub_left hs).sub_right hR

end Lay.Ok

/-! ## The words no step changes -/

/-- Our stack argument `j`. -/
def ourArg (L : Lay) : Nat → BitVec 64
  | 0 => L.dl | 1 => L.inp | 2 => L.il | 3 => L.p | 4 => L.pl | 5 => L.q | 6 => L.ql | 7 => L.dp
  | 8 => L.dpl | 9 => L.dq | 10 => L.dql | 11 => L.qi | 12 => L.qil | 13 => L.scr | _ => L.sl

/-- The words in the frames and our stack arguments that stay as they are
between the slots' writes and the frames' pops, with our return address
`lr`: the private-key operation's stack arguments (our own from `p` on),
the slots of our arguments, and our stack arguments. -/
structure Kept (L : Lay) (lr : BitVec 64) (m : Mem) : Prop where
  call : ∀ j < 12, m.readW (L.Q + BitVec.ofNat 64 (8 * j)) 64 = ourArg L (j + 3)
  out : m.readW (L.Q + BitVec.ofNat 64 oOut) 64 = L.out
  ml : m.readW (L.Q + BitVec.ofNat 64 oML) 64 = L.ml
  n : m.readW (L.Q + BitVec.ofNat 64 oN) 64 = L.n
  k : m.readW (L.Q + BitVec.ofNat 64 oK) 64 = L.k
  e : m.readW (L.Q + BitVec.ofNat 64 oE) 64 = L.e
  el : m.readW (L.Q + BitVec.ofNat 64 oEl) 64 = L.el
  d : m.readW (L.Q + BitVec.ofNat 64 oD) 64 = L.d
  dl : m.readW (L.Q + BitVec.ofNat 64 oDl) 64 = L.dl
  inp : m.readW (L.Q + BitVec.ofNat 64 oIn) 64 = L.inp
  scr : m.readW (L.Q + BitVec.ofNat 64 oScr) 64 = L.scr
  lr : m.readW (L.Q + BitVec.ofNat 64 208) 64 = lr
  args : ∀ j < 15, m.readW (L.Q + BitVec.ofNat 64 (224 + 8 * j)) 64 = ourArg L j

/-- The offsets of the kept words. -/
def keptOff (d : Nat) : Prop := (d + 8 ≤ 176) ∨ (208 ≤ d ∧ d + 8 ≤ 224) ∨ (224 ≤ d ∧ d + 8 ≤ 344)

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {lr : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L lr m)
    (hf : Frame rs m m')
    (hd : ∀ d, keptOff d → ∀ R ∈ rs, Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R) : Kept L lr m' := by
  have k : ∀ d, keptOff d →
      m'.readW (L.Q + BitVec.ofNat 64 d) 64 = m.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  refine ⟨fun j hj => (k _ (by unfold keptOff; omega)).trans (hk.call j hj), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, (k 208 (by unfold keptOff; omega)).trans hk.lr,
    fun j hj => (k _ (by unfold keptOff; omega)).trans (hk.args j hj)⟩
  exacts [(k oOut (by unfold keptOff oOut; omega)).trans hk.out, (k oML (by unfold keptOff oML; omega)).trans hk.ml,
    (k oN (by unfold keptOff oN; omega)).trans hk.n, (k oK (by unfold keptOff oK; omega)).trans hk.k,
    (k oE (by unfold keptOff oE; omega)).trans hk.e, (k oEl (by unfold keptOff oEl; omega)).trans hk.el,
    (k oD (by unfold keptOff oD; omega)).trans hk.d, (k oDl (by unfold keptOff oDl; omega)).trans hk.dl,
    (k oIn (by unfold keptOff oIn; omega)).trans hk.inp, (k oScr (by unfold keptOff oScr; omega)).trans hk.scr]

/-- A kept word misses a range in a writable buffer. -/
theorem Lay.Ok.kept_buf {L : Lay} (h : L.Ok) {d : Nat} (hd : keptOff d) {R : Region} (hR : InW L R) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := by
  unfold keptOff at hd
  rcases hd with hd | hd | hd
  · exact h.stk_buf (by omega) hR
  · exact h.stk_buf (by omega) hR
  · exact h.args_buf hd.1 hd.2 hR

/-! ## Between the frames' pushes and pops -/

/-- The state between the slots' writes and the frames' pops: `g` and `vv`
are the registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.D, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.ML, L.SCR]
  sp : t.sp = L.Q
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  kept : Kept L (g .x30) t.mem
  frame : Frame [L.OUT, L.ML, L.SCR, L.STK] m₀ t.mem

/-- A range code may write: in a writable buffer, or one of the frame's
changing slots (from `oR`). -/
def Wr (L : Lay) (r : Region) : Prop :=
  InW L r ∨ ∃ d, oR ≤ d ∧ d + r.len ≤ frameBytes ∧ r.base = L.Q + BitVec.ofNat 64 d

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t)
include hc

/-- Code that writes only registers other than the callee-saved ones and
the vector registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr, by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- Code that also writes memory where `Wr` allows. -/
theorem store (hL : L.Ok) {rs : List Region} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame rs t.mem t'.mem) (hin : ∀ r ∈ rs, Wr L r) : Ctx L g vv m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · rcases hin R hR with hw | ⟨d', h₁, h₂, hb⟩
    · exact hL.kept_buf hd hw
    · obtain ⟨b, n⟩ := R
      simp only at hb h₂; subst hb
      unfold keptOff at hd; unfold oR at h₁; unfold frameBytes at h₂
      exact hL.fr_sep (by omega) (by omega) (by omega)
  · rcases hin r hr with (hw | hw | hw) | ⟨d', h₁, h₂, hb⟩
    · exact ⟨L.OUT, by simp, hw⟩
    · exact ⟨L.ML, by simp, hw⟩
    · exact ⟨L.SCR, by simp, hw⟩
    · obtain ⟨b, n⟩ := r
      simp only at hb h₂; subst hb
      unfold frameBytes at h₂
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega)⟩

theorem inFr {d n : Nat} (hd : d + n ≤ frameBytes) : InRegions t.wr (L.Q + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩

theorem inFrR {d n : Nat} (hd : d + n ≤ frameBytes) : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩

end Ctx

/-- The registers a block writes, other than the callee-saved ones. -/
theorem mem_ne {l : List Reg} {r d : Reg} (hr : r ∈ l) (hd : d ∉ l) : r ≠ d := fun e => hd (e ▸ hr)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
