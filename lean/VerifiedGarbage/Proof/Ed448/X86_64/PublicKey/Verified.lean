import VerifiedGarbage.Impl.Ed448.X86_64.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout`. -/
section

/-!
# Ed448 public-key derivation on x86-64: where everything is

The function's buffers (`out`, `seed`, `scratch`) and the 104 bytes of stack
below its return address, from `B` up (`Lay`): the frame (88 bytes, from `B +
16`: the pruned scalar, then the pointers to `scratch`, `seed` and `out`) and
the 16 bytes below it that the calls use. `Ctx` is what holds between the
frame's push and pop: the permissions, `rsp`, the callee-saved registers, the
pointers in the frame, and that memory changed only in `out`, `scratch` and
the stack. `call_ok` runs a call of verified code in such a state.
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64

/-- The buffers and the lowest byte of the stack used (`rsp - 104` on entry). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  B : Addr

namespace Lay

variable (L : VG.Proof.Ed448.X86_64.PublicKey.Lay)

abbrev OUT : Region := ⟨L.out, 57⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 104⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 88⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 104, 8⟩

/-- What the contract says of where the buffers and the stack are. -/
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  ro : L.RET.Disjoint L.OUT
  rs : L.RET.Disjoint L.SEED
  rc : L.RET.Disjoint L.SCR
  no : L.out.toNat + 57 ≤ 2 ^ 64
  ns : L.seed.toNat + 57 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed448.X86_64.PublicKey.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Ed448.X86_64.PublicKey.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Ed448.X86_64.PublicKey.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_stk (B : Addr) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 104) :
    VG.Proof.Ed448.X86_64.PublicKey.Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 88⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : VG.Proof.Ed448.X86_64.PublicKey.Lay}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 104) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem seed_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.seed, 57⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.sc.sub_right (Offset.sub_base _ h₂)

theorem stk_SEED (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 104) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SEED := h.ks.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 104) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 104) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  VG.Proof.Ed448.X86_64.PublicKey.sub8 B

/-- The stack a call from `rsp = B + 16` uses, if it nests calls at most twice. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.SEED]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 80) 64 = L.scr
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 88) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 96) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

/-- A call of verified code (see `WP.call`), which nests calls at most once
more and is given regions within `seed`, the frame, `out` and `scratch` to
read and within `out` and `scratch` to write: afterwards `Ctx` holds again,
memory changed only within what it writes and the 16 bytes below `rsp`, and
the callee's postcondition holds. -/
theorem call_ok {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    refine Covers.of_sub fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simpa using hR
  have hcovw : Covers wr t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact VG.Proof.Ed448.X86_64.PublicKey.below_call_sub _ (by omega)
  -- The regions the call may change are disjoint from the pointers in the frame.
  have hdisj : ∀ d, 80 ≤ d → d + 8 ≤ 104 → ∀ r ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h₁ h₂ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 80 (by omega) (by omega)).trans hc.pScr,
    (keep 88 (by omega) (by omega)).trans hc.pSeed, (keep 96 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact ⟨_, by simp, h.sub⟩
      · exact ⟨_, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 104) (by omega)
      simpa using this

/-! ## The contract -/

/-- The x86-64 contract of `vg_ed448_public_key`: `Spec.Ed448.publicKeyContract`
for 104 bytes of stack, spelled out (`out = rdi`, `seed = rsi`, `scratch = rdx`). -/
def pkLocal : Contract isa where
  pre s := 104 ≤ (s.gpr .rsp).toNat ∧ s.rd = [⟨s.gpr .rsi, 57⟩] ∧
    s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rsi, 57⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 57⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 57⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 57⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 104, 104⟩ ⟨s.gpr .rdi, 57⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 104, 104⟩ ⟨s.gpr .rsi, 57⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 104, 104⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 57 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .rdi) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Ed448.X86_64.PublicKey.Lay := ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rsp - BitVec.ofNat 64 104⟩

theorem lay_ret (s : State) : (VG.Proof.Ed448.X86_64.PublicKey.lay s).B + BitVec.ofNat 64 104 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed448.X86_64.PublicKey.lay s).Ok := by
  obtain ⟨-, -, -, os, oc, sc, ro, rs, rc, ko, ks, kc, no, ns, nc⟩ := h
  have e : (VG.Proof.Ed448.X86_64.PublicKey.lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, VG.Proof.Ed448.X86_64.PublicKey.lay_ret]
  exact ⟨os, oc, sc, ko, ks, kc, e ▸ ro, e ▸ rs, e ▸ rc, no, ns, nc⟩

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (Impl.Ed448.X86_64.stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed448.X86_64.PublicKey.ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed448.X86_64.PublicKey.ofInt_nat]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of a region the return address of a call misses, on entry to the callee. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rsp_ce (t : State) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

/-- Callee-saved registers, through writes of others. -/
macro "cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

namespace Ctx

variable {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.frame⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [VG.Proof.Ed448.X86_64.PublicKey.sub8']

/-- The seed, as on entry. -/
theorem seed (hL : L.Ok) (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {i : Nat} (hi : i < 57) :
    t.mem (L.seed + BitVec.ofNat 64 i) = m₀ (L.seed + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.SEED) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.os.symm
    · exact hL.sc
    · exact hL.ks.symm) (by show (57 : Nat) ≤ 2 ^ 64; decide) hi

theorem inFr (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 104) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 104) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem inScrW (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

end Ctx

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 11) = sp - BitVec.ofNat 64 104 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 3) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 104 + BitVec.ofNat 64 (96 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : pkLocal.pre s) :
    VG.Proof.Ed448.X86_64.PublicKey.Ctx (VG.Proof.Ed448.X86_64.PublicKey.lay s) s.gpr s.mxcsr s.mem (pushed VG.Proof.Ed448.X86_64.PublicKey.pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 11 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Proof.Ed448.X86_64.PublicKey.pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 3), (pushed VG.Proof.Ed448.X86_64.PublicKey.pushRs s).mem.readW
      ((VG.Proof.Ed448.X86_64.PublicKey.lay s).B + BitVec.ofNat 64 (96 - 8 * j)) 64 = s.gpr (VG.Proof.Ed448.X86_64.PublicKey.pushRs[j]'(by show j < 11; omega)) := fun j hj => by
    rw [← hw j (by show j < 11; omega)]; simp only [VG.Proof.Ed448.X86_64.PublicKey.lay]; rw [VG.Proof.Ed448.X86_64.PublicKey.push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [List.length_cons, List.length_nil, VG.Proof.Ed448.X86_64.PublicKey.lay]; rw [VG.Proof.Ed448.X86_64.PublicKey.push_base]
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, VG.Proof.Ed448.X86_64.PublicKey.lay]; rw [VG.Proof.Ed448.X86_64.PublicKey.push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(VG.Proof.Ed448.X86_64.PublicKey.lay s).STK, by simp, ?_⟩
    simp only [List.length_cons, List.length_nil]
    rw [VG.Proof.Ed448.X86_64.PublicKey.push_base]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ed448.X86_64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Hash`. -/
section

/-!
# Ed448 public-key derivation on x86-64: the hash of the seed

From the state after the frame's push: the Keccak state at `scratch` zeroed
(`zero_ok`), then the calls of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` (rate 136, SHAKE's suffix), with their working space at
`scratch + 256`, leave `SHAKE256(seed, 114)` at `scratch + 1024`
(`hash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Spec.Sha3 (stateAt)

variable {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- Code that writes only caller-saved registers and within `scratch`. -/
theorem Ctx.scrw (hL : L.Ok) {t t' : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    {rs : List Region} (hrs : ∀ r ∈ rs, VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR) (hf : Frame rs t.mem t'.mem) :
    VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' := by
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _)
      (fun r hr => (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right (hrs r hr).sub) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 80 (by omega) (by omega)).trans hc.pScr, (keep 88 (by omega) (by omega)).trans hc.pSeed,
    (keep 96 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => ⟨L.SCR, by simp, (hrs r hr).sub⟩)⟩

/-- The Keccak state at `scratch`, on entry to a call from the frame. -/
theorem Ctx.ce_state (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    stateAt t.callEntry.mem L.scr = stateAt t.mem L.scr :=
  Proof.Sha3.stateAt_congr fun _ hi => VG.Proof.Ed448.X86_64.PublicKey.ce_byte t (R := ⟨L.scr, 200⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega))
    (by show (200 : Nat) ≤ 2 ^ 64; decide) hi

/-- The seed on entry to a call from the frame. -/
theorem Ctx.ce_seed (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    Spec.Sha3.bytesAt t.callEntry.mem L.seed 57 = Spec.Sha3.bytesAt m₀ L.seed 57 := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [VG.Proof.Ed448.X86_64.PublicKey.ce_byte t (R := L.SEED) (by rw [hc.ret]; exact hL.stk_SEED (by omega))
    (by show (57 : Nat) ≤ 2 ^ 64; decide) hi]
  exact hc.seed hL hi

/-! ## Zeroing the state -/

theorem zeroHead_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkZeroHead) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = L.scr ∧ t'.gpr .rax = 0 := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkZeroHead, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, State.load64,
    State.setReg32, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceAdd, h80,
    Option.some.injEq, exists_eq_left', hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl⟩

theorem zstore_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hdi : t.gpr .rdi = L.scr) {k : Nat} (hk : k < 25) :
    WP isa (.block [Instr.store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax]) t fun t' =>
      t'.mem = t.mem.writeW (L.scr + BitVec.ofNat 64 (8 * k)) (t.gpr .rax) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inScrW (o := 8 * k) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, VG.Proof.Ed448.X86_64.PublicKey.ea_base, hdi, w, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The stores of `pkZeroStores`, the first `n`. -/
abbrev zstores (n : Nat) : List Instr :=
  (List.range n).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax

theorem zstores_ok (hL : L.Ok) : ∀ n ≤ 25, ∀ t : State, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t → t.gpr .rdi = L.scr →
    t.gpr .rax = 0 → WP isa (.block (VG.Proof.Ed448.X86_64.PublicKey.zstores n)) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.gpr .rdi = L.scr ∧ t'.gpr .rax = 0 ∧ Frame [⟨L.scr, 200⟩] t.mem t'.mem ∧
        ∀ j < n, t'.mem.readW (L.scr + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, _, hc, h1, h2 => WP.block_nil ⟨hc, h1, h2, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc, h1, h2 => by
    rw [VG.Proof.Ed448.X86_64.PublicKey.zstores, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zstores_ok hL n (by omega) t hc h1 h2) fun u ⟨hu, u1, u2, uf, uz⟩ => ?_
    refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zstore_ok hu u1 (k := n) (by omega)) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.scr, 200⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    refine ⟨hu.scrw hL vrd vwr vmx (fun r _ => by rw [vg])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)) hf1,
      by rw [vg]; exact u1, by rw [vg]; exact u2, uf.trans hf1, fun j hj => ?_⟩
    rw [vm, u2]
    by_cases hjk : j = n
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uz j (by omega)]

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zero_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa pkZeroState t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ stateAt t'.mem L.scr = Spec.Sha3.zero := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zeroHead_ok hc) fun u ⟨hu, _, u1, u2⟩ => ?_)
  exact WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zstores_ok hL 25 (by omega) u hu u1 u2) fun v ⟨hv, _, _, _, hz⟩ => ⟨hv, VG.Proof.Ed448.X86_64.PublicKey.zero_state hz⟩

/-! ## The sponge functions -/

theorem absorb_nosp : NoSp Impl.Sha3.X86_64.Stream.absorb := by
  have : ((instrs Impl.Sha3.X86_64.Stream.absorb).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem pad_nosp : NoSp Impl.Sha3.X86_64.Stream.pad := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem squeeze_nosp : NoSp Impl.Sha3.X86_64.Stream.squeeze := by
  have : ((instrs Impl.Sha3.X86_64.Stream.squeeze).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem absorb_depth : Impl.Sha3.X86_64.Stream.absorb.depth ≤ 1 := by decide +kernel
theorem pad_depth : Impl.Sha3.X86_64.Stream.pad.depth ≤ 1 := by decide +kernel
theorem squeeze_depth : Impl.Sha3.X86_64.Stream.squeeze.depth ≤ 1 := by decide +kernel

/-! ## `absorb` -/

/-- What the call of `absorb` needs of the registers. -/
def AbsArgs (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 0 ∧
    t.gpr .rcx = L.seed ∧ t.gpr .r8 = BitVec.ofNat 64 57 ∧ t.gpr .r9 = L.scr + BitVec.ofNat 64 256

theorem absArgs_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkAbsorbArgs) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed448.X86_64.PublicKey.AbsArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  have h88 := hc.inFr (d := 88) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkAbsorbArgs, scrPtr, keccakScratch, fScratch, fSeed, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add,
    Nat.reduceAdd, h80, h88, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSeed, VG.Proof.Ed448.X86_64.PublicKey.AbsArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, trivial, by decide,
    by rw [VG.Proof.Ed448.X86_64.PublicKey.sx32 (by omega)]⟩

abbrev absRd (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region := [L.SEED]
abbrev absWr (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region := [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem abs_regs {t : State} (ha : VG.Proof.Ed448.X86_64.PublicKey.AbsArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.seed ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = BitVec.ofNat 64 57 ∧
      (t.callEntry.withRegions rd wr).gpr .r9 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.2⟩

theorem abs_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.AbsArgs L t) :
    Proof.Sha3.absorbX86_64.pre (t.callEntry.withRegions (VG.Proof.Ed448.X86_64.PublicKey.absRd L) (VG.Proof.Ed448.X86_64.PublicKey.absWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := VG.Proof.Ed448.X86_64.PublicKey.abs_regs ha (VG.Proof.Ed448.X86_64.PublicKey.absRd L) (VG.Proof.Ed448.X86_64.PublicKey.absWr L)
  simp only [Proof.Sha3.absorbX86_64, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, hdi, hsi, hdx, hcx, h8, h9, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.sub8, VG.Proof.Ed448.X86_64.PublicKey.sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.seed_scr (e := 0) (k := 200) (by omega), hL.seed_scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_SEED (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem abs_sub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.absRd L ++ VG.Proof.Ed448.X86_64.PublicKey.absWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SEED, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega)⟩

theorem abs_wsub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.absWr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega))

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem abs_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.AbsArgs L t)
    (hz : stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Sha3.Repr t'.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) := by
  refine VG.Proof.Ed448.X86_64.PublicKey.call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct VG.Proof.Ed448.X86_64.PublicKey.absorb_nosp VG.Proof.Ed448.X86_64.PublicKey.absorb_depth hc
    (VG.Proof.Ed448.X86_64.PublicKey.abs_pre hL hc ha) VG.Proof.Ed448.X86_64.PublicKey.abs_sub VG.Proof.Ed448.X86_64.PublicKey.abs_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost, _⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, h8, -⟩ := VG.Proof.Ed448.X86_64.PublicKey.abs_regs ha (VG.Proof.Ed448.X86_64.PublicKey.absRd L) (VG.Proof.Ed448.X86_64.PublicKey.absWr L)
  simp only [State.withRegions_mem, hdi, hsi, hdx, hcx, h8, hm, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hpost
  have h := hpost [] (VG.Proof.Ed448.X86_64.PublicKey.repr_nil (by rw [hc.ce_state hL, hz])) rfl
  rwa [List.nil_append, hc.ce_seed hL] at h

theorem abs_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hz : stateAt t.mem L.scr = Spec.Sha3.zero) :
    WP isa (callWith pkAbsorbArgs "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha3.Repr t'.mem L.scr 136 (Spec.Sha3.bytesAt m₀ L.seed 57) :=
  WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.absArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => VG.Proof.Ed448.X86_64.PublicKey.abs_call hL hc₁ ha (hm₁ ▸ hz))

/-! ## `pad` -/

/-- What the call of `pad` needs of the registers. -/
def PadArgs (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 57 ∧
    t.gpr .rcx = BitVec.ofNat 64 0x1f ∧ t.gpr .r8 = L.scr + BitVec.ofNat 64 256

theorem padArgs_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkPadArgs) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed448.X86_64.PublicKey.PadArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPadArgs, scrPtr, keccakScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add,
    Nat.reduceAdd, h80, Option.some.injEq, exists_eq_left', hc.pScr, VG.Proof.Ed448.X86_64.PublicKey.PadArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, by decide,
    by rw [VG.Proof.Ed448.X86_64.PublicKey.sx32 (by omega)]⟩

abbrev padRd : List Region := []
abbrev padWr (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region := [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem pad_regs {t : State} (ha : VG.Proof.Ed448.X86_64.PublicKey.PadArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 57 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = BitVec.ofNat 64 0x1f ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem pad_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.PadArgs L t) :
    Proof.Sha3.padX86_64.pre (t.callEntry.withRegions VG.Proof.Ed448.X86_64.PublicKey.padRd (VG.Proof.Ed448.X86_64.PublicKey.padWr L)) := by
  obtain ⟨hdi, hsi, hdx, -, h8⟩ := VG.Proof.Ed448.X86_64.PublicKey.pad_regs ha VG.Proof.Ed448.X86_64.PublicKey.padRd (VG.Proof.Ed448.X86_64.PublicKey.padWr L)
  simp only [Proof.Sha3.padX86_64, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, hdi, hsi, hdx, h8, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.sub8, VG.Proof.Ed448.X86_64.PublicKey.sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem pad_sub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.padRd ++ VG.Proof.Ed448.X86_64.PublicKey.padWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega)⟩

theorem pad_wsub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.padWr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR := VG.Proof.Ed448.X86_64.PublicKey.abs_wsub

theorem pad_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.PadArgs L t) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem L.scr 136 msg) (hl : msg.length = 57) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      stateAt t'.mem L.scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  refine VG.Proof.Ed448.X86_64.PublicKey.call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct VG.Proof.Ed448.X86_64.PublicKey.pad_nosp VG.Proof.Ed448.X86_64.PublicKey.pad_depth hc
    (VG.Proof.Ed448.X86_64.PublicKey.pad_pre hL hc ha) VG.Proof.Ed448.X86_64.PublicKey.pad_sub VG.Proof.Ed448.X86_64.PublicKey.pad_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, -⟩ := VG.Proof.Ed448.X86_64.PublicKey.pad_regs ha VG.Proof.Ed448.X86_64.PublicKey.padRd (VG.Proof.Ed448.X86_64.PublicKey.padWr L)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, hdi, hsi, hdx, hcx, hm, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at hpost
  have hr' : Spec.Sha3.Repr t.callEntry.mem L.scr 136 msg := by unfold Spec.Sha3.Repr; rw [hc.ce_state hL]; exact hr
  rw [hpost msg hr' (by rw [hl])]
  rfl

theorem pad_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {msg : List Byte}
    (hr : Spec.Sha3.Repr t.mem L.scr 136 msg) (hl : msg.length = 57) :
    WP isa (callWith pkPadArgs "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
        stateAt t'.mem L.scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) :=
  WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.padArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => VG.Proof.Ed448.X86_64.PublicKey.pad_call hL hc₁ ha (hm₁ ▸ hr) hl)

/-! ## `squeeze` -/

/-- What the call of `squeeze` needs of the registers. -/
def SqzArgs (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 136 ∧ t.gpr .rdx = BitVec.ofNat 64 0 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 1024 ∧ t.gpr .r8 = BitVec.ofNat 64 114 ∧
    t.gpr .r9 = L.scr + BitVec.ofNat 64 256

theorem sqzArgs_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkSqueezeArgs) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed448.X86_64.PublicKey.SqzArgs L t' := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkSqueezeArgs, scrPtr, keccakScratch, hashAt, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.load64, State.setReg32, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp,
    VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceAdd, h80, Option.some.injEq, exists_eq_left', hc.pScr, VG.Proof.Ed448.X86_64.PublicKey.SqzArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by decide, by decide, by rw [VG.Proof.Ed448.X86_64.PublicKey.sx32 (by omega)],
    by decide, by rw [VG.Proof.Ed448.X86_64.PublicKey.sx32 (by omega)]⟩

abbrev sqzRd : List Region := []
abbrev sqzWr (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region :=
  [⟨L.scr, 200⟩, ⟨L.scr + BitVec.ofNat 64 1024, 114⟩, ⟨L.scr + BitVec.ofNat 64 256, 640⟩]

theorem sqz_regs {t : State} (ha : VG.Proof.Ed448.X86_64.PublicKey.SqzArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 136 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = BitVec.ofNat 64 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.scr + BitVec.ofNat 64 1024 ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = BitVec.ofNat 64 114 ∧
      (t.callEntry.withRegions rd wr).gpr .r9 = L.scr + BitVec.ofNat 64 256 :=
  ⟨(VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2.2⟩

theorem sqz_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.SqzArgs L t) :
    Proof.Sha3.squeezeX86_64.pre (t.callEntry.withRegions VG.Proof.Ed448.X86_64.PublicKey.sqzRd (VG.Proof.Ed448.X86_64.PublicKey.sqzWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := VG.Proof.Ed448.X86_64.PublicKey.sqz_regs ha VG.Proof.Ed448.X86_64.PublicKey.sqzRd (VG.Proof.Ed448.X86_64.PublicKey.sqzWr L)
  simp only [Proof.Sha3.squeezeX86_64, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, hdi, hsi, hdx, hcx, h8, h9, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.sub8, VG.Proof.Ed448.X86_64.PublicKey.sub88,
    State.withRegions_rd, State.withRegions_wr, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega), Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 200) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 1024) (k := 114) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 256) (k := 640) (by omega) (by omega),
    by decide, by decide⟩

theorem sqz_sub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.sqzRd ++ VG.Proof.Ed448.X86_64.PublicKey.sqzWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega)⟩

theorem sqz_wsub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.sqzWr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega))
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_off _ (by omega))

theorem sqz_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.SqzArgs L t) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 := by
  refine VG.Proof.Ed448.X86_64.PublicKey.call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct VG.Proof.Ed448.X86_64.PublicKey.squeeze_nosp VG.Proof.Ed448.X86_64.PublicKey.squeeze_depth hc
    (VG.Proof.Ed448.X86_64.PublicKey.sqz_pre hL hc ha) VG.Proof.Ed448.X86_64.PublicKey.sqz_sub VG.Proof.Ed448.X86_64.PublicKey.sqz_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost, _⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, h8, -⟩ := VG.Proof.Ed448.X86_64.PublicKey.sqz_regs ha VG.Proof.Ed448.X86_64.PublicKey.sqzRd (VG.Proof.Ed448.X86_64.PublicKey.sqzWr L)
  simp only [State.withRegions_mem, hdi, hsi, hdx, hcx, h8, hm, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hpost
  rw [hpost, hc.ce_state hL]

theorem sqz_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (callWith pkSqueezeArgs "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem L.scr) 0 114 :=
  WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.sqzArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => by rw [← hm₁]; exact VG.Proof.Ed448.X86_64.PublicKey.sqz_call hL hc₁ ha)

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [VG.Proof.Ed448.X86_64.PublicKey.squeezeFrom_zero]; rfl

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `SHAKE256(seed, 114)` at `scratch + 1024`. -/
theorem hash_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa pkHash t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Sha3.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zero_ok hL hc) fun t₁ ⟨hc₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.abs_step hL hc₁ hz₁) fun t₂ ⟨hc₂, hr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.pad_step hL hc₂ hr₂ (VG.Proof.Ed448.X86_64.PublicKey.bytesAt_length _ _ _)) fun t₃ ⟨hc₃, hs₃⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.sqz_step hL hc₃) fun t₄ ⟨hc₄, hb₄⟩ => ⟨hc₄, ?_⟩
  rw [hb₄, hs₃, VG.Proof.Ed448.X86_64.PublicKey.shake256_eq]

end VG.Proof.Ed448.X86_64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Base`. -/
section

/-!
# Ed448 public-key derivation on x86-64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored in the frame
(`prune_ok`), `[s]B` is encoded into `out` (`base_ok`), and the frame's copy
of `s` is cleared (`wipe_ok`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 (prune_nat)

variable {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Stores into the frame -/

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem) : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' := by
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 80 (by omega) (by omega)).trans hc.pScr, (keep 88 (by omega) (by omega)).trans hc.pSeed,
    (keep 96 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩)⟩

theorem st_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {k : Nat} (hk : k < 8) (r : Reg) :
    WP isa (.block [Instr.store (stk (8 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * k)) (t.gpr r) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inFrW (d := 16 + 8 * k) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add, w,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The first `n` stores of `pkStores`. -/
abbrev storesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (8 * k)) (pkRegs.getD k .r8)

theorem stores_ok : ∀ n ≤ 8, ∀ t : State, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t →
    WP isa (.block (VG.Proof.Ed448.X86_64.PublicKey.storesN n)) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem ∧
      ∀ j < n, t'.mem.readW (L.B + BitVec.ofNat 64 (16 + 8 * j)) 64 = t.gpr (pkRegs.getD j .r8)
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc => by
    rw [VG.Proof.Ed448.X86_64.PublicKey.storesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.stores_ok n (by omega) t hc) fun u ⟨hu, ug, uf, uw⟩ => ?_
    refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.st_ok hu (k := n) (by omega) _) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega)
        (by omega))
    refine ⟨hu.store vrd vwr vmx (fun r _ => by rw [vg]) hf1, by rw [vg, ug], uf.trans hf1, fun j hj => ?_⟩
    rw [vm]
    by_cases hjn : j = n
    · subst hjn; rw [Mem.readW_writeW_self64, ug]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uw j (by omega)]

/-! ## Pruning -/

/-- Word `k` of the hash. -/
abbrev hw (t : State) (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1024 + 8 * k)) 64

/-- `rdx = scratch`. -/
theorem rdx_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block [Instr.mov .rdx (.mem (stk fScratch))]) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdx = L.scr := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, VG.Proof.Ed448.X86_64.PublicKey.ea_stk,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, Option.map_some, ite_true, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceAdd, h80,
    hc.pScr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial⟩

theorem loads_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (hdx : t.gpr .rdx = L.scr) :
    WP isa (.block pkLoads) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = VG.Proof.Ed448.X86_64.PublicKey.hw t L 0 ∧ t'.gpr .r9 = VG.Proof.Ed448.X86_64.PublicKey.hw t L 1 ∧ t'.gpr .r10 = VG.Proof.Ed448.X86_64.PublicKey.hw t L 2 ∧ t'.gpr .r11 = VG.Proof.Ed448.X86_64.PublicKey.hw t L 3 ∧
      t'.gpr .rax = VG.Proof.Ed448.X86_64.PublicKey.hw t L 4 ∧ t'.gpr .rcx = VG.Proof.Ed448.X86_64.PublicKey.hw t L 5 ∧ t'.gpr .rsi = VG.Proof.Ed448.X86_64.PublicKey.hw t L 6 := by
  have s0 := hc.inScr (o := 1024) (by omega)
  have s1 := hc.inScr (o := 1032) (by omega)
  have s2 := hc.inScr (o := 1040) (by omega)
  have s3 := hc.inScr (o := 1048) (by omega)
  have s4 := hc.inScr (o := 1056) (by omega)
  have s5 := hc.inScr (o := 1064) (by omega)
  have s6 := hc.inScr (o := 1072) (by omega)
  apply WP.of_runBlock
  simp only [pkLoads, hashWord, hashAt, Nat.reduceMul, Nat.reduceAdd, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.load64, VG.Proof.Ed448.X86_64.PublicKey.ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, hdx,
    s0, s1, s2, s3, s4, s5, s6, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

theorem mods_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkMods) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (t.gpr .r8 &&& BitVec.ofNat 64 (2 ^ 64 - 4)) ∧ t'.gpr .r9 = t.gpr .r9 ∧
      t'.gpr .r10 = t.gpr .r10 ∧ t'.gpr .r11 = t.gpr .r11 ∧ t'.gpr .rax = t.gpr .rax ∧
      t'.gpr .rcx = t.gpr .rcx ∧ t'.gpr .rsi = (t.gpr .rsi ||| BitVec.ofNat 64 (2 ^ 63)) ∧
      t'.gpr .rdi = 0 := by
  apply WP.of_runBlock
  simp only [pkMods, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-4)) = BitVec.ofNat 64 (2 ^ 64 - 4)),
    trivial, trivial, trivial, trivial, trivial, trivial, rfl⟩

/-- The loads, the pruning and the stores, with `rdx = scratch`. -/
theorem pruneRest_ok {t₀ : State} (hc₀ : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t₀) (hd₀ : t₀.gpr .rdx = L.scr) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t₀.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa (.block (pkLoads ++ (pkMods ++ pkStores))) t₀ fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.loads_ok hc₀ hd₀) fun u ⟨hu, hmu, u8, u9, u10, u11, uax, ucx, usi⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.mods_ok hu) fun v ⟨hv, hmv, v8, v9, v10, v11, vax, vcx, vsi, vdi⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.stores_ok 8 (by omega) v hv) fun w ⟨hw', _, _, ww⟩ => ⟨hw', ?_⟩
  have f0 : w.mem.readW (L.B + BitVec.ofNat 64 16) 64 = v.gpr .r8 := ww 0 (by omega)
  have f1 : w.mem.readW (L.B + BitVec.ofNat 64 24) 64 = v.gpr .r9 := ww 1 (by omega)
  have f2 : w.mem.readW (L.B + BitVec.ofNat 64 32) 64 = v.gpr .r10 := ww 2 (by omega)
  have f3 : w.mem.readW (L.B + BitVec.ofNat 64 40) 64 = v.gpr .r11 := ww 3 (by omega)
  have f4 : w.mem.readW (L.B + BitVec.ofNat 64 48) 64 = v.gpr .rax := ww 4 (by omega)
  have f5 : w.mem.readW (L.B + BitVec.ofNat 64 56) 64 = v.gpr .rcx := ww 5 (by omega)
  have f6 : w.mem.readW (L.B + BitVec.ofNat 64 64) 64 = v.gpr .rsi := ww 6 (by omega)
  have f7 : w.mem.readW (L.B + BitVec.ofNat 64 72) 64 = v.gpr .rdi := ww 7 (by omega)
  rw [VG.Proof.Ed448.X86_64.decode57]
  simp only [VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceAdd]
  rw [f0, f1, f2, f3, f4, f5, f6, byte_of_zero _ _ (f7.trans vdi), v8, v9, v10, v11, vax, vcx, vsi, u8, u9,
    u10, u11, uax, ucx, usi, Spec.Ed448.prune, ← hh, take57, VG.Proof.Ed448.X86_64.decode57]
  simp only [VG.Proof.Ed448.X86_64.PublicKey.hw, VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceMul, Nat.reduceAdd]
  refine Eq.trans ?_ (prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm
  have c₁ : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  have c₂ : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, c₁, c₂]

theorem prune_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa pkPrune t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h :=
  WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.rdx_ok hc) fun _ ⟨hc₀, hm₀, hd₀⟩ => VG.Proof.Ed448.X86_64.PublicKey.pruneRest_ok hc₀ hd₀ (hm₀ ▸ hh))

/-! ## The base point -/

/-- The arguments of `vg_ed448_scalar_base`. -/
def BaseArgs (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed448.X86_64.PublicKey.BaseArgs L t' := by
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inFr (d := 96) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, VG.Proof.Ed448.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.add_add, Nat.reduceAdd, l80, l96,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, VG.Proof.Ed448.X86_64.PublicKey.BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem base_nosp : NoSp scalarBase := by
  have : ((instrs scalarBase).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem base_depth : scalarBase.depth ≤ 1 := by lit_decide

abbrev baseRd (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 57⟩]
abbrev baseWr (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : VG.Proof.Ed448.X86_64.PublicKey.BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed448.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed448.X86_64.PublicKey.BaseArgs L t) :
    Proof.Ed448.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (VG.Proof.Ed448.X86_64.PublicKey.baseRd L) (VG.Proof.Ed448.X86_64.PublicKey.baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := VG.Proof.Ed448.X86_64.PublicKey.base_regs ha (VG.Proof.Ed448.X86_64.PublicKey.baseRd L) (VG.Proof.Ed448.X86_64.PublicKey.baseWr L)
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, g3, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, hc.rsp, VG.Proof.Ed448.X86_64.PublicKey.sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.oc, hL.nc⟩

theorem base_sub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.baseRd L ++ VG.Proof.Ed448.X86_64.PublicKey.baseWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_stk _ (by omega) (by omega)⟩
  · exact ⟨L.OUT, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ VG.Proof.Ed448.X86_64.PublicKey.baseWr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed448.X86_64.PublicKey.within_base _ (by omega))

theorem base_ok (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t)
    (ha : VG.Proof.Ed448.X86_64.PublicKey.BaseArgs L t) {s : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57) = s) :
    WP isa (.call "vg_ed448_scalar_base" scalarBase) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul s Spec.Ed448.basePoint) := by
  refine VG.Proof.Ed448.X86_64.PublicKey.call_ok hL (Proof.Ed448.X86_64.scalarBase_ok hb) VG.Proof.Ed448.X86_64.PublicKey.base_nosp VG.Proof.Ed448.X86_64.PublicKey.base_depth hc
    (VG.Proof.Ed448.X86_64.PublicKey.base_pre hL hc ha) VG.Proof.Ed448.X86_64.PublicKey.base_sub VG.Proof.Ed448.X86_64.PublicKey.base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := VG.Proof.Ed448.X86_64.PublicKey.base_regs ha (VG.Proof.Ed448.X86_64.PublicKey.baseRd L) (VG.Proof.Ed448.X86_64.PublicKey.baseWr L)
  have h := hpost
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed448.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 57 =
      Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact VG.Proof.Ed448.X86_64.PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 57⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by show (57 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed448.scalarBase, hs]

/-! ## Clearing the scalar -/

theorem zero_regs_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block (pkRegs.map fun r => Instr.mov32 r (.imm 0))) t fun t' =>
      VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkRegs, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zero_regs_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (VG.Proof.Ed448.X86_64.PublicKey.stores_ok 8 (by omega) u hu) fun u' ⟨hu', _, hf, _⟩ => ⟨hu', hm ▸ hf⟩

end VG.Proof.Ed448.X86_64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified`. -/
section

/-!
# Ed448 public-key derivation on x86-64: `Verified`

The frame's body leaves the public key in `out` (`body_ok`), and the whole
function meets `pkLocal` and the ABI (`publicKey_ok`), given that the
reference ladder encodes `[k]B` (`BaseLadderOk`, which the registration file
passes in).

Constant time: two runs whose pointers agree have the same layout, so between
the frame's push and pop they are related by `Two`: both satisfy `Ctx` with
that layout (and `Φ`, what the next block or call needs of the registers),
whatever their secrets. The blocks address only the stack and `scratch`, from
registers that agree (the taint analysis); each call is of constant-time code
whose public data, its pointers and lengths, agree (`RelCT.callEx`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64

variable {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Correctness -/

/-- The public key of the seed in `out`. -/
theorem body_ok (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa pkBody t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.hash_ok hL hc) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.prune_ok hc₁ hh₁) fun t₂ ⟨hc₂, hs₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.baseArgs_ok hc₂) fun t₃ ⟨hc₃, hm₃, ha₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.base_ok hb hL hc₃ ha₃ (hm₃ ▸ hs₂)) fun t₄ ⟨hc₄, ho₄⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.PublicKey.wipe_ok hc₄) fun t₅ ⟨hc₅, hf₅⟩ => ⟨hc₅, ?_⟩
  have e : Spec.Ed448.bytesAt t₅.mem L.out 57 = Spec.Ed448.bytesAt t₄.mem L.out 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact Frame.bytes (R := L.OUT) hf₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (d := 16) (n := 64) (by omega)).symm) (by show (57 : Nat) ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  rw [e, ho₄]
  rfl

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 11) = B + BitVec.ofNat 64 104 := by
  rw [VG.Proof.Ed448.X86_64.PublicKey.add_add]

/-- `vg_ed448_public_key` meets `pkLocal` and the ABI. -/
theorem publicKey_ok (hb : Proof.Ed448.BaseLadderOk) {s : State} (h : pkLocal.pre s) :
    WP isa publicKey s fun s' => abiPreserved s s' ∧ pkLocal.post s s' := by
  have hL := VG.Proof.Ed448.X86_64.PublicKey.lay_ok h
  have hc := VG.Proof.Ed448.X86_64.PublicKey.push_ctx h
  refine WP.frame (rs := VG.Proof.Ed448.X86_64.PublicKey.pushRs) (by decide) (by decide) (by decide) (by show 8 * 11 ≤ _; have := h.1; omega)
    (WP.mono (VG.Proof.Ed448.X86_64.PublicKey.body_ok hb hL hc) fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 11 from rfl, VG.Proof.Ed448.X86_64.PublicKey.pop_rsp, VG.Proof.Ed448.X86_64.PublicKey.lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (VG.Proof.Ed448.X86_64.PublicKey.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (VG.Proof.Ed448.X86_64.PublicKey.lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, VG.Proof.Ed448.X86_64.PublicKey.lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed448.bytesAt (popped .rax pushRs.length u).mem (VG.Proof.Ed448.X86_64.PublicKey.lay s).out 57 = _
    rw [popped_mem, ho]
    rfl

/-! ## Constant time -/

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Two.Env := VG.Proof.Ed448.X86_64.PublicKey.Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ VG.Proof.Ed448.X86_64.PublicKey.Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧
    VG.Proof.Ed448.X86_64.PublicKey.Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧ Φ e.1 a ∧ Φ e.1 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop}
    (hct : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      WP isa c t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) c (VG.Proof.Ed448.X86_64.PublicKey.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_block {is : List Instr} {Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rsp_two {L : VG.Proof.Ed448.X86_64.PublicKey.Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {mx₁ mx₂ : BitVec 32} {m₁ m₂ : Mem}
    (c₁ : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁) (c₂ : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

theorem covers {t : State} (hc : VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call, with the same regions in both runs. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Ed448.X86_64.PublicKey.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR) :
    RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂, (VG.Proof.Ed448.X86_64.PublicKey.covers c₁ (hsub L) (hwsub L)).1, (VG.Proof.Ed448.X86_64.PublicKey.covers c₁ (hsub L) (hwsub L)).2,
      (VG.Proof.Ed448.X86_64.PublicKey.covers c₂ (hsub L) (hwsub L)).1, (VG.Proof.Ed448.X86_64.PublicKey.covers c₂ (hsub L) (hwsub L)).2, VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂⟩

/-- A block, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      WP isa (.block is) t fun t' => VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) (.block is) (VG.Proof.Ed448.X86_64.PublicKey.Two Ψ) :=
  VG.Proof.Ed448.X86_64.PublicKey.two_wp (VG.Proof.Ed448.X86_64.PublicKey.two_block rs hrs h) hw

/-- A call of verified code, after which `Ctx` holds again. -/
theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : VG.Proof.Ed448.X86_64.PublicKey.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed448.X86_64.PublicKey.Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, VG.Proof.Ed448.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed448.X86_64.PublicKey.Within r L.SCR) :
    RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two Φ) (.call n c) (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) :=
  VG.Proof.Ed448.X86_64.PublicKey.two_wp (VG.Proof.Ed448.X86_64.PublicKey.two_call hv hct rd wr hpre hpub hsub hwsub) fun L _ _ _ _ hL hc hf =>
    VG.Proof.Ed448.X86_64.PublicKey.call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (hsub L) (hwsub L) fun _ hc' _ _ _ => ⟨hc', trivial⟩

theorem rspOnly {Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop} : ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂

/-- `rsp` and the register `r`, which `Φ` fixes for the layout. -/
theorem rspAnd {Φ : VG.Proof.Ed448.X86_64.PublicKey.Lay → State → Prop} (r : Reg) (v : VG.Proof.Ed448.X86_64.PublicKey.Lay → BitVec 64) (hv : ∀ L t, Φ L t → t.gpr r = v L) :
    ∀ (L : VG.Proof.Ed448.X86_64.PublicKey.Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed448.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ x ∈ [Reg.rsp, r], t₁.gpr x = t₂.gpr x := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ f₁ f₂ x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂
  · exact (hv L t₁ f₁).trans (hv L t₂ f₂).symm

/-- The frame's body. -/
theorem body_ct (hb : Proof.Ed448.BaseLadderOk) : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) pkBody fun _ _ => True := by
  -- zeroing the state
  have z₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkZeroHead)
      (VG.Proof.Ed448.X86_64.PublicKey.Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zeroHead_ok hc) fun _ ⟨hc', _, h1, h2⟩ => ⟨hc', h1, h2⟩
  have z₂ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) (.block pkZeroStores)
      (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_wp (VG.Proof.Ed448.X86_64.PublicKey.two_block [.rsp, .rdi] (VG.Proof.Ed448.X86_64.PublicKey.rspAnd .rdi Lay.scr fun _ _ h => h.1) (by taint_decide))
      fun _ _ _ _ t hL hc hf => WP.mono (VG.Proof.Ed448.X86_64.PublicKey.zstores_ok hL 25 (by omega) t hc hf.1 hf.2) fun _ h => ⟨h.1, trivial⟩
  -- `absorb`
  have a₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkAbsorbArgs) (VG.Proof.Ed448.X86_64.PublicKey.Two VG.Proof.Ed448.X86_64.PublicKey.AbsArgs) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.absArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have a₂ := VG.Proof.Ed448.X86_64.PublicKey.two_callP (n := "vg_keccak_absorb_scratch") (Φ := VG.Proof.Ed448.X86_64.PublicKey.AbsArgs)
    Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    VG.Proof.Ed448.X86_64.PublicKey.absorb_nosp VG.Proof.Ed448.X86_64.PublicKey.absorb_depth VG.Proof.Ed448.X86_64.PublicKey.absRd VG.Proof.Ed448.X86_64.PublicKey.absWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed448.X86_64.PublicKey.abs_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := VG.Proof.Ed448.X86_64.PublicKey.abs_regs a₁ (VG.Proof.Ed448.X86_64.PublicKey.absRd L) (VG.Proof.Ed448.X86_64.PublicKey.absWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := VG.Proof.Ed448.X86_64.PublicKey.abs_regs a₂ (VG.Proof.Ed448.X86_64.PublicKey.absRd L) (VG.Proof.Ed448.X86_64.PublicKey.absWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂]⟩)
    (fun _ => VG.Proof.Ed448.X86_64.PublicKey.abs_sub) (fun _ => VG.Proof.Ed448.X86_64.PublicKey.abs_wsub)
  -- `pad`
  have p₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkPadArgs) (VG.Proof.Ed448.X86_64.PublicKey.Two VG.Proof.Ed448.X86_64.PublicKey.PadArgs) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.padArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p₂ := VG.Proof.Ed448.X86_64.PublicKey.two_callP (n := "vg_keccak_pad_scratch") (Φ := VG.Proof.Ed448.X86_64.PublicKey.PadArgs)
    Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    VG.Proof.Ed448.X86_64.PublicKey.pad_nosp VG.Proof.Ed448.X86_64.PublicKey.pad_depth (fun _ => VG.Proof.Ed448.X86_64.PublicKey.padRd) VG.Proof.Ed448.X86_64.PublicKey.padWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed448.X86_64.PublicKey.pad_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, -, r₁⟩ := VG.Proof.Ed448.X86_64.PublicKey.pad_regs a₁ VG.Proof.Ed448.X86_64.PublicKey.padRd (VG.Proof.Ed448.X86_64.PublicKey.padWr L)
      obtain ⟨d₂, s₂, x₂, -, r₂⟩ := VG.Proof.Ed448.X86_64.PublicKey.pad_regs a₂ VG.Proof.Ed448.X86_64.PublicKey.padRd (VG.Proof.Ed448.X86_64.PublicKey.padWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, r₁.trans r₂.symm,
        by rw [VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂]⟩)
    (fun _ => VG.Proof.Ed448.X86_64.PublicKey.pad_sub) (fun _ => VG.Proof.Ed448.X86_64.PublicKey.pad_wsub)
  -- `squeeze`
  have q₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkSqueezeArgs) (VG.Proof.Ed448.X86_64.PublicKey.Two VG.Proof.Ed448.X86_64.PublicKey.SqzArgs) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.sqzArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have q₂ := VG.Proof.Ed448.X86_64.PublicKey.two_callP (n := "vg_keccak_squeeze_scratch") (Φ := VG.Proof.Ed448.X86_64.PublicKey.SqzArgs)
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    VG.Proof.Ed448.X86_64.PublicKey.squeeze_nosp VG.Proof.Ed448.X86_64.PublicKey.squeeze_depth (fun _ => VG.Proof.Ed448.X86_64.PublicKey.sqzRd) VG.Proof.Ed448.X86_64.PublicKey.sqzWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed448.X86_64.PublicKey.sqz_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := VG.Proof.Ed448.X86_64.PublicKey.sqz_regs a₁ VG.Proof.Ed448.X86_64.PublicKey.sqzRd (VG.Proof.Ed448.X86_64.PublicKey.sqzWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := VG.Proof.Ed448.X86_64.PublicKey.sqz_regs a₂ VG.Proof.Ed448.X86_64.PublicKey.sqzRd (VG.Proof.Ed448.X86_64.PublicKey.sqzWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂]⟩)
    (fun _ => VG.Proof.Ed448.X86_64.PublicKey.sqz_sub) (fun _ => VG.Proof.Ed448.X86_64.PublicKey.sqz_wsub)
  -- pruning
  have r₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block [Instr.mov .rdx (.mem (stk fScratch))])
      (VG.Proof.Ed448.X86_64.PublicKey.Two fun L t => t.gpr .rdx = L.scr) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.rdx_ok hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩
  have r₂ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun L t => t.gpr .rdx = L.scr) (.block (pkLoads ++ (pkMods ++ pkStores)))
      (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_wp (VG.Proof.Ed448.X86_64.PublicKey.two_block [.rsp, .rdx] (VG.Proof.Ed448.X86_64.PublicKey.rspAnd .rdx Lay.scr fun _ _ h => h) (by taint_decide))
      fun _ _ _ _ _ _ hc hd => WP.mono (VG.Proof.Ed448.X86_64.PublicKey.pruneRest_ok hc hd rfl) fun _ h => ⟨h.1, trivial⟩
  -- the base point
  have b₁ : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkBaseArgs) (VG.Proof.Ed448.X86_64.PublicKey.Two VG.Proof.Ed448.X86_64.PublicKey.BaseArgs) :=
    VG.Proof.Ed448.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed448.X86_64.PublicKey.baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ := VG.Proof.Ed448.X86_64.PublicKey.two_callP (n := "vg_ed448_scalar_base") (Φ := VG.Proof.Ed448.X86_64.PublicKey.BaseArgs)
    (Proof.Ed448.X86_64.scalarBase_ok hb) Proof.Ed448.X86_64.scalarBase_ct
    VG.Proof.Ed448.X86_64.PublicKey.base_nosp VG.Proof.Ed448.X86_64.PublicKey.base_depth VG.Proof.Ed448.X86_64.PublicKey.baseRd VG.Proof.Ed448.X86_64.PublicKey.baseWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed448.X86_64.PublicKey.base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := VG.Proof.Ed448.X86_64.PublicKey.base_regs a₁ (VG.Proof.Ed448.X86_64.PublicKey.baseRd L) (VG.Proof.Ed448.X86_64.PublicKey.baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := VG.Proof.Ed448.X86_64.PublicKey.base_regs a₂ (VG.Proof.Ed448.X86_64.PublicKey.baseRd L) (VG.Proof.Ed448.X86_64.PublicKey.baseWr L)
      exact ⟨by rw [VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_ce, VG.Proof.Ed448.X86_64.PublicKey.rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (fun _ => VG.Proof.Ed448.X86_64.PublicKey.base_sub) (fun _ => VG.Proof.Ed448.X86_64.PublicKey.base_wsub)
  have w : RelCT isa (VG.Proof.Ed448.X86_64.PublicKey.Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    VG.Proof.Ed448.X86_64.PublicKey.two_block [.rsp] VG.Proof.Ed448.X86_64.PublicKey.rspOnly (by taint_decide)
  exact ((z₁.seq z₂).seq ((a₁.seq a₂).seq ((p₁.seq p₂).seq (q₁.seq q₂)))).seq
    ((r₁.seq r₂).seq (b₁.seq (b₂.seq w)))

theorem publicKey_ct (hb : Proof.Ed448.BaseLadderOk) : ConstantTime isa pkLocal.pre pkLocal.pub publicKey := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1) (RelCT.mono (VG.Proof.Ed448.X86_64.PublicKey.body_ct hb) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx⟩, rfl, rfl⟩
  have e : VG.Proof.Ed448.X86_64.PublicKey.lay s₂ = VG.Proof.Ed448.X86_64.PublicKey.lay s₁ := by simp only [VG.Proof.Ed448.X86_64.PublicKey.lay, hsp, hdi, hsi, hdx]
  exact ⟨⟨VG.Proof.Ed448.X86_64.PublicKey.lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, VG.Proof.Ed448.X86_64.PublicKey.lay_ok h₁, VG.Proof.Ed448.X86_64.PublicKey.push_ctx h₁,
    e ▸ VG.Proof.Ed448.X86_64.PublicKey.push_ctx h₂, trivial, trivial⟩

/-! ## The shared contract -/

theorem implies : pkLocal.Implies (Spec.Ed448.publicKeyContract X86_64.abi 104) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords,
    X86_64.abi, X86_64.argRegs, VG.Proof.Ed448.X86_64.PublicKey.pkLocal] [Proof.Ed448.X86_64.scalarBaseSat]
    using Proof.Ed448.X86_64.scalarBaseSat

theorem publicKey_verified (hb : Proof.Ed448.BaseLadderOk) :
    Verified X86_64.target publicKey (Spec.Ed448.publicKeyContract X86_64.abi 104) :=
  Verified.of_correct (fun _ h => VG.Proof.Ed448.X86_64.PublicKey.publicKey_ok hb h) (VG.Proof.Ed448.X86_64.PublicKey.publicKey_ct hb) VG.Proof.Ed448.X86_64.PublicKey.implies

end VG.Proof.Ed448.X86_64.PublicKey

end
