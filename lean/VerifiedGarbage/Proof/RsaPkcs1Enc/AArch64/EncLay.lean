import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callee
import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Encrypt
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: where everything is

The contract the proof is written against (`encK`, with `P` bytes of stack
for the call below the frames), the function's buffers and its stack, from
the inner frame's base `Q` (`Lay`): below it the `P` bytes the call uses
(`LOW`), from it the inner frame (`FR`: the call's stack arguments, the
slots and `EM`), the frame holding our return address (`LR`, from
`Q + 1072`) and our stack arguments (`ARGS`, from `Q + 1088`). `Ctx` is what
holds between the frames' pushes and pops once the slots are written, and
`Kept` the words in them that no step changes.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- `vg_rsa_pkcs1_encrypt(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, msg = x6, msg_len = x7, ps, ps_len, scratch, scratch_len)`, the
last four on the stack, with `P + 1088` bytes of stack below `sp`. -/
def encK (P : Nat) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let msg : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let ps : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 (P + 1088), P + 1088⟩
    P + 1088 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ 2 ^ 64 ∧ s.rd = [n, e, msg, ps, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint msg ∧ out.Disjoint ps ∧ out.Disjoint scr ∧
      out.Disjoint args ∧ n.Disjoint scr ∧ e.Disjoint scr ∧ msg.Disjoint scr ∧ ps.Disjoint scr ∧
      scr.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint msg ∧ stk.Disjoint ps ∧
      stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat + 11 ≤ (s.gpr .x3).toNat ∧
      (stackArg s 1).toNat = (s.gpr .x3).toNat - (s.gpr .x7).toNat - 3 ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

namespace Enc

open VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- The arguments, the inner frame's base `Q` and the bytes `P` below it the
call uses. -/
structure Lay where
  out : Addr
  ol : BitVec 64
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  msg : Addr
  ml : BitVec 64
  ps : Addr
  pl : BitVec 64
  scr : Addr
  sl : BitVec 64
  Q : Addr
  P : Nat

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, L.k.toNat⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.ml.toNat⟩
abbrev PS : Region := ⟨L.ps, L.pl.toNat⟩
abbrev SCR : Region := ⟨L.scr, L.sl.toNat * 8⟩
/-- The inner frame, the frame of our return address, our stack arguments. -/
abbrev FR : Region := ⟨L.Q, frameBytes⟩
abbrev LR : Region := ⟨L.Q + BitVec.ofNat 64 1072, 16⟩
abbrev ARGS : Region := ⟨L.Q + BitVec.ofNat 64 1088, 32⟩
/-- The stack the call uses, and all the stack used. -/
abbrev LOW : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
abbrev STK : Region := ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 1088⟩
/-- `EM`, `k` bytes. -/
abbrev EM : Region := ⟨L.Q + BitVec.ofNat 64 oEM, L.k.toNat⟩

/-- What the contract says of where the buffers and the stack are, and of
the lengths. -/
structure Ok : Prop where
  oN : L.OUT.Disjoint L.N
  oE : L.OUT.Disjoint L.E
  oM : L.OUT.Disjoint L.MSG
  oP : L.OUT.Disjoint L.PS
  oS : L.OUT.Disjoint L.SCR
  oA : L.OUT.Disjoint L.ARGS
  nS : L.N.Disjoint L.SCR
  eS : L.E.Disjoint L.SCR
  mS : L.MSG.Disjoint L.SCR
  pS : L.PS.Disjoint L.SCR
  sA : L.SCR.Disjoint L.ARGS
  kO : L.STK.Disjoint L.OUT
  kN : L.STK.Disjoint L.N
  kE : L.STK.Disjoint L.E
  kM : L.STK.Disjoint L.MSG
  kP : L.STK.Disjoint L.PS
  kS : L.STK.Disjoint L.SCR
  bO : L.out.toNat + L.k.toNat ≤ 2 ^ 64
  bN : L.n.toNat + L.k.toNat ≤ 2 ^ 64
  bE : L.e.toNat + L.el.toNat ≤ 2 ^ 64
  bM : L.msg.toNat + L.ml.toNat ≤ 2 ^ 64
  bP : L.ps.toNat + L.pl.toNat ≤ 2 ^ 64
  bS : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  nQ : L.Q.toNat + 1120 ≤ 2 ^ 64
  pQ : L.P ≤ L.Q.toNat
  kv : Spec.Rsa.lenValid L.k.toNat
  olk : L.ol.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  mlk : L.ml.toNat + 11 ≤ L.k.toNat
  plk : L.pl.toNat = L.k.toNat - L.ml.toNat - 3
  slk : Spec.Rsa.scratchWords L.k.toNat ≤ L.sl.toNat

end Lay

/-! ## Offsets from `Q` -/

theorem q_add (Q : Addr) (P d : Nat) :
    Q + BitVec.ofNat 64 d = Q - BitVec.ofNat 64 P + BitVec.ofNat 64 (P + d) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The offsets of the kept words. -/
def keptOff (d : Nat) : Prop := (d + 8 ≤ 32) ∨ (1072 ≤ d ∧ d + 8 ≤ 1088) ∨ (1088 ≤ d ∧ d + 8 ≤ 1120)

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem k64 : 64 ≤ L.k.toNat := h.kv.1
theorem k1024 : L.k.toNat ≤ 1024 := h.kv.2

omit h in
/-- A range in our stack is in `STK`. -/
theorem sub_stk {d n : Nat} (hd : d + n ≤ 1088) : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.STK := by
  rw [q_add L.Q L.P d]; exact Offset.sub_base _ (by omega)

omit h in
theorem low_stk : Region.Sub L.LOW L.STK := Region.sub_prefix (by omega)

/-- A range in our stack misses a buffer the contract keeps apart from it. -/
theorem stk_buf {d n : Nat} (hd : d + n ≤ 1088) {R : Region}
    (hR : R = L.OUT ∨ R = L.N ∨ R = L.E ∨ R = L.MSG ∨ R = L.PS ∨ R = L.SCR) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ R := by
  have hs := Lay.Ok.sub_stk (L := L) hd
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h.kO.sub_left hs, h.kN.sub_left hs, h.kE.sub_left hs, h.kM.sub_left hs, h.kP.sub_left hs,
    h.kS.sub_left hs]

/-- Two ranges in our stack and arguments, apart. -/
theorem fr_sep {d n d' n' : Nat} (hs : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 1120) (h₂ : d' + n' ≤ 1120) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ ⟨L.Q + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ hs (by have := h.nQ; omega) (by have := h.nQ; omega)

/-- A range in our frames misses the stack the call uses. -/
theorem fr_low {d n : Nat} (hd : d + n ≤ 1120) : Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
  Offset.disjoint_below _ (by have := h.nQ; have := h.pQ; omega)

/-- Our stack arguments miss a writable buffer. -/
theorem args_out : L.ARGS.Disjoint L.OUT := h.oA.symm
theorem args_scr : L.ARGS.Disjoint L.SCR := h.sA.symm

/-- A kept word misses a range within `out` or `scratch`. -/
theorem kept_buf {d : Nat} (hd : keptOff d) {R : Region} (hR : Region.Sub R L.OUT ∨ Region.Sub R L.SCR) :
    Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := by
  unfold keptOff at hd
  by_cases h₁ : d + 8 ≤ 1088
  · rcases hR with hs | hs
    · exact (h.stk_buf h₁ (.inl rfl)).sub_right hs
    · exact (h.stk_buf h₁ (.inr (.inr (.inr (.inr (.inr rfl)))))).sub_right hs
  · have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ L.ARGS := Offset.sub _ (by omega) (by omega)
    rcases hR with hR | hR
    · exact (h.args_out.sub_left hs).sub_right hR
    · exact (h.args_scr.sub_left hs).sub_right hR

end Lay.Ok

/-! ## The words no step changes -/

/-- The words in the frames and our stack arguments that stay as they are
between the frames' pushes and pops, with our return address `lr`. -/
structure Kept (L : Lay) (lr : BitVec 64) (m : Mem) : Prop where
  scr : m.readW (L.Q + BitVec.ofNat 64 0) 64 = L.scr
  sl : m.readW (L.Q + BitVec.ofNat 64 8) 64 = L.sl
  out : m.readW (L.Q + BitVec.ofNat 64 oOut) 64 = L.out
  k : m.readW (L.Q + BitVec.ofNat 64 oK) 64 = L.k
  lr : m.readW (L.Q + BitVec.ofNat 64 1072) 64 = lr
  ps : m.readW (L.Q + BitVec.ofNat 64 (arg 0)) 64 = L.ps
  pl : m.readW (L.Q + BitVec.ofNat 64 (arg 1)) 64 = L.pl
  ascr : m.readW (L.Q + BitVec.ofNat 64 (arg 2)) 64 = L.scr
  asl : m.readW (L.Q + BitVec.ofNat 64 (arg 3)) 64 = L.sl

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {lr : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L lr m)
    (hf : Frame rs m m')
    (hd : ∀ d, keptOff d → ∀ R ∈ rs, Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R) : Kept L lr m' := by
  have k : ∀ d, keptOff d →
      m'.readW (L.Q + BitVec.ofNat 64 d) 64 = m.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 0 (by unfold keptOff; omega)).trans hk.scr, (k 8 (by unfold keptOff; omega)).trans hk.sl,
    (k oOut (by unfold keptOff oOut; omega)).trans hk.out, (k oK (by unfold keptOff oK; omega)).trans hk.k,
    (k 1072 (by unfold keptOff; omega)).trans hk.lr,
    (k _ (by unfold keptOff arg frameBytes; omega)).trans hk.ps,
    (k _ (by unfold keptOff arg frameBytes; omega)).trans hk.pl,
    (k _ (by unfold keptOff arg frameBytes; omega)).trans hk.ascr,
    (k _ (by unfold keptOff arg frameBytes; omega)).trans hk.asl⟩

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops, once the slots are
written: `g` and `vv` are the registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.MSG, L.PS, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.Q
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  kept : Kept L (g .x30) t.mem
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

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

/-- Code that also writes memory in the inner frame, apart from the kept
words. -/
theorem store (hL : L.Ok) {rs : List Region} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame rs t.mem t'.mem)
    (hin : ∀ r ∈ rs, ∃ d, 32 ≤ d ∧ d + r.len ≤ 1072 ∧ r.base = L.Q + BitVec.ofNat 64 d) :
    Ctx L g vv m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · obtain ⟨d', h₁, h₂, hb⟩ := hin R hR
    obtain ⟨b, n⟩ := R
    simp only at hb h₂; subst hb
    unfold keptOff at hd
    exact hL.fr_sep (by omega) (by omega) (by omega)
  · obtain ⟨d', h₁, h₂, hb⟩ := hin r hr
    obtain ⟨b, n⟩ := r
    simp only at hb h₂; subst hb
    exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega)⟩

theorem inFr {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions t.wr (L.Q + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩

theorem inFrR {d n : Nat} (hd : d + n ≤ frameBytes) : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩

theorem inArgs (hL : L.Ok) {d : Nat} (h₁ : 1088 ≤ d) (h₂ : d + 8 ≤ 1120) :
    InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nQ; omega)⟩

end Ctx

/-- The registers a block writes, other than the callee-saved ones. -/
macro "enc_cs_tac" : tactic => `(tactic| (
  intro r hr _
  revert hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, reduceCtorEq, ite_false]))

/-- Side conditions of reads and writes at offsets from `Q`. -/
macro "enc_disch" : tactic => `(tactic| first
  | decide
  | (apply Offset.sep <;> omega)
  | omega)

end Enc

end VG.Proof.RsaPkcs1Enc.AArch64
