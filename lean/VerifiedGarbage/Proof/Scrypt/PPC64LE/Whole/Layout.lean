module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# scrypt on PPC64LE: where everything is

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Steps.lean`): the function's
buffers and the 1120 bytes of stack below the stack pointer, from `B` up
(`Lay`): the 1008 bytes the calls use, then the frame (from `B + 1008`: its
32-byte header, then from `B + 1040` our return address, our caller's `r30`,
the password, its length, `r`, `b`, `blen`, `v` and the next block). Our
stack arguments are at `B + 1216`. `Ctx` is what holds in the frame's body,
and `call_ok` runs a call of verified code in such a state.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE

/-- The arguments, and the lowest byte of the stack used (`sp - 1120` on
entry). -/
structure Lay where
  pw : Addr
  pwl : BitVec 64
  salt : Addr
  sl : BitVec 64
  r : BitVec 64
  b : Addr
  blen : BitVec 64
  v : Addr
  vlen : BitVec 64
  scr : Addr
  slen : BitVec 64
  out : Addr
  ol : BitVec 64
  B : Addr

namespace Lay

variable (L : Lay)

abbrev PW : Region := ⟨L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 1216, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 1120⟩
/-- The frame's local variable space. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 1040, 80⟩
/-- The frame's stack pointer. -/
abbrev E : Addr := L.B + BitVec.ofNat 64 1008

/-- `p` and `N`. -/
abbrev pp : Nat := L.blen.toNat / L.r.toNat
abbrev NN : Nat := L.vlen.toNat / L.r.toNat

/-- What the contract says of where the buffers and the stack are, and of
the parameters. -/
structure Ok : Prop where
  pb : L.PW.Disjoint L.BB
  pv : L.PW.Disjoint L.VV
  pc : L.PW.Disjoint L.SC
  po : L.PW.Disjoint L.OUT
  sb : L.SALT.Disjoint L.BB
  sv : L.SALT.Disjoint L.VV
  sc : L.SALT.Disjoint L.SC
  so : L.SALT.Disjoint L.OUT
  bv : L.BB.Disjoint L.VV
  bc : L.BB.Disjoint L.SC
  bo : L.BB.Disjoint L.OUT
  ba : L.BB.Disjoint L.ARGS
  vc : L.VV.Disjoint L.SC
  vo : L.VV.Disjoint L.OUT
  va : L.VV.Disjoint L.ARGS
  co : L.SC.Disjoint L.OUT
  ca : L.SC.Disjoint L.ARGS
  oa : L.OUT.Disjoint L.ARGS
  kp : L.STK.Disjoint L.PW
  ks : L.STK.Disjoint L.SALT
  kb : L.STK.Disjoint L.BB
  kv : L.STK.Disjoint L.VV
  kc : L.STK.Disjoint L.SC
  ko : L.STK.Disjoint L.OUT
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 64
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 64
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 64
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 64
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 64
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  nB : L.B.toNat + 1256 ≤ 2 ^ 64
  rpos : 0 < L.r.toNat
  bmod : L.blen.toNat % L.r.toNat = 0
  vmod : L.vlen.toNat % L.r.toNat = 0
  valid : Spec.Scrypt.valid L.NN L.r.toNat L.pp L.ol.toNat
  olb : L.ol.toNat ≤ (2 ^ 32 - 1) * 32
  slen : L.slen.toNat = L.r.toNat + 16

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 1120) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 1216 ≤ d) (h₂ : d + n ≤ 1256) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hr
  · exact (h.va.symm.sub_left hs).sub_right hr
  · exact (h.ca.symm.sub_left hs).sub_right hr
  · exact (h.oa.symm.sub_left hs).sub_right hr

end Lay.Ok

/-! ## What the calls cannot change -/

/-- The doublewords of the frame and our stack arguments that stay as they
are in the frame's body: our return address `lr` and our caller's `r30`. -/
structure Kept (L : Lay) (lr r30 : BitVec 64) (m : Mem) : Prop where
  lr : m.readW (L.B + BitVec.ofNat 64 1040) 64 = lr
  r30 : m.readW (L.B + BitVec.ofNat 64 1048) 64 = r30
  pw : m.readW (L.B + BitVec.ofNat 64 1056) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 1064) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 1072) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 1080) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 1088) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 1096) 64 = L.v
  vlen : m.readW (L.B + BitVec.ofNat 64 1216) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 1224) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 1240) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 1248) 64 = L.ol

/-- Where the kept doublewords are. -/
abbrev KeptAt (d : Nat) : Prop := (1040 ≤ d ∧ d + 8 ≤ 1104) ∨ (1216 ≤ d ∧ d + 8 ≤ 1256)

/-- The kept doublewords survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {lr r30 : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L lr r30 m)
    (hf : Frame rs m m')
    (hd : ∀ d, KeptAt d → ∀ R ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : Kept L lr r30 m' := by
  have k : ∀ d, KeptAt d →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 1040 (by decide)).trans hk.lr, (k 1048 (by decide)).trans hk.r30, (k 1056 (by decide)).trans hk.pw,
    (k 1064 (by decide)).trans hk.pwl, (k 1072 (by decide)).trans hk.r, (k 1080 (by decide)).trans hk.b,
    (k 1088 (by decide)).trans hk.blen, (k 1096 (by decide)).trans hk.v, (k 1216 (by decide)).trans hk.vlen,
    (k 1224 (by decide)).trans hk.scr, (k 1240 (by decide)).trans hk.out, (k 1248 (by decide)).trans hk.ol⟩

/-! ## In the frame's body -/

/-- The state in the frame's body: `g` are the registers on entry, `lr` the
return address, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (lr : BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.E
  r30 : t.gpr .r30 = L.E
  cs : ∀ r ∈ preserved, r ≠ .r30 → t.gpr r = g r
  kept : Kept L lr (g .r30) t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : Lay) (r : Region) : Prop :=
  Within r L.BB ∨ Within r L.VV ∨ Within r L.SC ∨ Within r L.OUT

theorem InBuf.sub {L : Lay} {r : Region} (h : InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

theorem covers {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g lr m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- The stack a call from `sp = B + 1008` uses, if it uses at most 1008 bytes. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 1008) :
    Region.Sub (below (B + BitVec.ofNat 64 1008) m) ⟨B, 1008⟩ := by
  have : B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (1008 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 1008) (a := m) (b := 1008) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-- A call of verified code (see `WP.callAny`), which uses at most 1008 bytes
of stack and is given regions within ours to read, and within the writable
buffers to write: afterwards `Ctx` holds again, memory changed only within
what it writes and the 1008 bytes below `sp`, and the callee's postcondition
holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 1008) {t : State} (hc : Ctx L g lr m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g lr m₀ s' → Frame (wr ++ [⟨L.B, 1008⟩]) t.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = t.gpr r) →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callAny hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs hpost => ?_) (by omega)
  have hf' : Frame (wr ++ [⟨L.B, 1008⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.sp]
      exact below_call_sub _ hd
  have hnB := hL.nB
  -- The regions the call may change miss the kept doublewords.
  have hdisj : ∀ d, KeptAt d → ∀ R ∈ wr ++ [⟨L.B, 1008⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega) hR' hs
      · exact hL.args_buf (by omega) (by omega) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hcs _ (by decide)).trans hc.r30,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hc.kept.frame hf' hdisj,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hcs hpost
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
    rcases hR' with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Region.sub_prefix (by decide)⟩

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r6, s.gpr .r7, s.gpr .r8, s.gpr .r9, s.gpr .r10,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    s.sp - BitVec.ofNat 64 1120⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 1120 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 1216 = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : scryptPPC.pre s) : (lay s).Ok := by
  obtain ⟨hst, h136, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 1256 ≤ 2 ^ 64 := by
    simp only [lay]
    simp only [stackBytes] at hst
    rw [Offset.toNat_sub_ofNat s.sp 1120]
    omega
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.PPC64LE.Whole
