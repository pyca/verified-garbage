module

import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.CombConstants
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! ### `Ed25519.X86_64.PublicKey.Hash`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.X86_64.PublicKey.Layout`. -/

@[expose] public section

section
/-!
# Ed25519 public-key derivation on x86-64: where everything is

The function's buffers (`out`, `seed`, `scratch`) and the 72 bytes of stack
below its return address, from `B` up (`Lay`): the frame (56 bytes, from `B +
16`: the pruned scalar, then the pointers to `scratch`, `seed` and `out`) and
the 16 bytes below it that the calls use. `Ctx` is what holds between the
frame's push and pop: the permissions, `rsp`, the callee-saved registers, the
pointers in the frame, and that memory changed only in `out`, `scratch` and
the stack. `call_ok` runs a call of verified code in such a state.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (combSym combWords combWordCount)
open VG.Proof.Ed25519.X86_64 (combRegion CombHeld)

/-- The buffers, the lowest byte of the stack used (`rsp - 72` on entry), and the comb's
tables (the static `combSym`). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  B : Addr
  T : Addr
  /-- The bytes read at `seed`: the seed (32), or its SHA-512 digest (64). -/
  seedLen : Nat

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, L.seedLen⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 72⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 56⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 72, 8⟩
/-- The comb's tables. -/
abbrev TBL : Region := combRegion L.T

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
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + L.seedLen ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  tbo : L.TBL.Disjoint L.OUT
  tbc : L.TBL.Disjoint L.SCR
  tbk : L.TBL.Disjoint L.STK
  tbr : L.TBL.Disjoint L.RET
  nt : L.T.toNat + 8 * combWordCount ≤ 2 ^ 64
  sl : 32 ≤ L.seedLen

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

theorem within_stk (B : Addr) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 72) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 56⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_using [h₁, h₂]⟩

namespace Lay.Ok

variable {L : Lay}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  sub8 B

/-- The stack a call from `rsp = B + 16` uses, if it nests calls at most twice. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega_using [hm])

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.SEED, L.TBL]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = L.scr
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 56) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 64) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sym : t.syms combSym = L.T
  held : ∀ i < combWordCount, m₀.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0

/-- A call of verified code (see `WP.call`), which nests calls at most once
more and is given regions within `seed`, the frame, `out` and `scratch` to
read and within `out` and `scratch` to write: afterwards `Ctx` holds again,
memory changed only within what it writes and the 16 bytes below `rsp`, and
the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.TBL, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.OUT ∨ Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
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
  refine WP.of_syms (WP.call_mx hv hsp (by omega_using [hd]) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx hsy => ?_)
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  -- The regions the call may change are disjoint from the pointers in the frame.
  have hdisj : ∀ d, 48 ≤ d → d + 8 ≤ 72 → ∀ r ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h₁ h₂ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 48 (by omega_using []) (by omega_using [])).trans hc.pScr,
    (keep 56 (by omega_using []) (by omega_using [])).trans hc.pSeed, (keep 64 (by omega_using []) (by omega_using [])).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_), hsy.symm ▸ hc.sym, hc.held⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact ⟨_, by simp, h.sub⟩
      · exact ⟨_, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 72) (by omega_using [])
      simpa using this

/-! ## The contract -/

/-- The x86-64 contract of public-key derivation for 72 bytes of stack, spelled out
(`out = rdi`, the `n` bytes of the seed or its digest at `rsi`, `scratch = rdx`), with
the condition `key` on them and the postcondition `post`. -/
def pkLocalWith (n : Nat) (key : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s := 72 ≤ (s.gpr .rsp).toNat ∧ s.rd = [⟨s.gpr .rsi, n⟩, combRegion (s.syms combSym)] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, n⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, n⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, n⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rsi, n⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + n ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧ key s ∧
    CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩,
      ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩]
  post := post
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.syms combSym = s₂.syms combSym

/-- The layout of a call from `s`. -/
def lay (n : Nat) (s : State) : Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rsp - BitVec.ofNat 64 72, s.syms combSym, n⟩

theorem lay_ret (n : Nat) (s : State) : (lay n s).B + BitVec.ofNat 64 72 = s.gpr .rsp :=
  BitVec.sub_add_cancel _ _

theorem lay_ok {n : Nat} {key : State → Prop} {post : State → State → Prop} {s : State}
    (h : (pkLocalWith n key post).pre s) (hn : 32 ≤ n) : (lay n s).Ok := by
  obtain ⟨-, -, -, os, oc, sc, ro, rs, rc, ko, ks, kc, no, ns, nc, -, hh⟩ := h
  obtain ⟨-, nt, hd⟩ := hh
  have e : (lay n s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  have h1 := hd ⟨s.gpr .rdi, 32⟩ (by simp)
  have h2 := hd ⟨s.gpr .rdx, 8192⟩ (by simp)
  have h3 := hd ⟨s.gpr .rsp, 8⟩ (by simp)
  have h4 := hd ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ (by simp)
  exact ⟨os, oc, sc, ko, ks, kc, e ▸ ro, e ▸ rs, e ▸ rc, no, ns, nc, h1, h2, h4, e ▸ h3, nt, hn⟩

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 on x86-64: the frame, and the SHA-512 functions it calls

The state after the frame's push (`push_ctx`), and what the calls of `init`, `update` and
`finalize` need, for any implementation `v` of the compression function.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

/-- Byte `i` of a region the return address of a call misses, on entry to the callee. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_using []) (by omega_using [])))
    (by simpa using hd.symm) hR hi

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) :
    Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.frame, by rw [hsy]; exact hc.sym, hc.held⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [sub8']

theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inScr (hc : Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_using [h])⟩

end Ctx

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 7) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 3) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 (64 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega_using [hj]
  bv_omega

theorem pushed_syms_eq (s : State) (rs : List Reg) : (pushed rs s).syms = s.syms := pushRegs_syms s rs

theorem push_ctx {n : Nat} {key : State → Prop} {post : State → State → Prop} {s : State}
    (h : (pkLocalWith n key post).pre s) :
    Ctx (lay n s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega_using [this]
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 3), (pushed pushRs s).mem.readW
      ((lay n s).B + BitVec.ofNat 64 (64 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 7; omega_using [hj])) := fun j hj => by
    rw [← hw j (by show j < 7; omega_using [hj])]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 2 (by omega_using []), hw' 1 (by omega_using []), hw' 0 (by omega_using []), ?_, congrFun (pushed_syms_eq s pushRs) combSym,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · rw [pushed_wr, h.2.2.1]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay n s).STK, by simp, ?_⟩
    simp only [List.length_cons, List.length_nil]
    rw [push_base]
    exact Offset.sub_base _ (by omega_using [])

/-! ## `init` -/

theorem nosp_init (iv : Spec.Sha512.HashValue) : NoSp (Impl.Sha512.X86_64.Stream.init iv) := by
  intro i hi
  rw [Proof.Sha512.X86_64.Stream.init_eq] at hi
  simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rsp_ce (t : State) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

/-- Callee-saved registers, through writes of others. -/
tactic_template "cs_tac" : tactic => `(tactic| (
                   intro r hr
                   revert hr
                   simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
                   rintro (h | h | h | h | h | h | h) <;> subst h <;>
                     simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## `update` and `finalize`, for any compression function -/

/-- SHA-512 with the compression function `v`, as `MdHash` builds it. -/
abbrev hashOf (v : Compress) : Impl.Pbkdf2.Md.X86_64.Hash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.hash Spec.Hmac.sha512I 64 "vg_sha512_init_core"
    Spec.Sha512.H0_512 v

theorem callees (v : Compress) : Proof.Pbkdf2.Md.X86_64.Callees (hashOf v) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.callees (Or.inr (Or.inl rfl)) v

theorem coreOK (v : Compress) : Proof.Pbkdf2.Md.X86_64.CoreOK (Proof.Pbkdf2.Md.X86_64.core (hashOf v)) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512C v

theorem upd_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.updateOwn v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).updMx (coreOK v)

theorem fin_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.finalizeOwn v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).finMx (coreOK v)

theorem upd_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.updateOwn v.callee) :=
  (callees v).updSp (coreOK v)

theorem fin_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.finalizeOwn v.callee) :=
  (callees v).finSp (coreOK v)

theorem upd_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.updateOwn v.callee).depth ≤ 1 :=
  (callees v).updD (coreOK v)

theorem fin_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.finalizeOwn v.callee).depth ≤ 1 :=
  (callees v).finD (coreOK v)

theorem upd_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.updateOwn v.callee) Proof.Sha512.updateX86_64 :=
  Proof.Sha512.X86_64.Stream.updateOwn_verified v.hso v.okS (upd_mx v)
    Proof.Sha512.X86_64.Shared.updateScratchImplies.sat_left

theorem fin_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalizeOwn v.callee) Proof.Sha512.finalizeX86_64 :=
  Proof.Sha512.X86_64.Stream.finalizeOwn_verified v.hso v.okS (fin_mx v)
    Proof.Sha512.X86_64.Shared.finalizeScratchImplies.sat_left

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.X86_64.PublicKey

end

end

/-! ### `Ed25519.X86_64.BaseCallee`, which this module and modules that import it used -/

section

/-!
# The base-point multiplications the Ed25519 functions call

`EdBase bs`: `bs` is a body of `vg_ed25519_scalar_base`, correct and constant
time for its contract (for states whose buffers are apart from the 8 bytes below
`rsp`, where its call of `vg_gf25519_r64_invert` stores its return address),
and its every instruction keeps `rsp` (the calls need both) in one level of
calls: those of `scalarBase_precomputed` (each field
multiplication), `scalarBase_adx` and `scalarBase_ifma`. Public-key derivation and signing are
proven once for any of them.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- The 8 bytes below `rsp = B + 8`, where a call from it stores its return address. -/
theorem hole_add8 (B : Addr) : hole (B + BitVec.ofNat 64 8) = ⟨B, 8⟩ := by
  simp only [hole]
  rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.add_sub_cancel]

class EdBase (bs : Prog isa) : Prop where
  ok : ∀ s, scalarBaseLocal.clear.pre s →
    ∃ t s', Exec isa bs s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s'
  ct : ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub bs
  instrs : bs.allInstrs (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true
  depth : bs.depth ≤ 1

instance {fld : Arith} [EdArith fld] [X25519.X86_64.DivstepInv] : EdBase (scalarBase_precomputed fld) :=
  ⟨scalarBase_precomputed_ok, scalarBase_precomputed_ctC, by fld_lit_decide, by fld_lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_adx :=
  ⟨scalarBase_adx_ok, scalarBase_adx_ct, by lit_decide, by lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_ifma :=
  ⟨Ifma.scalarBase_ifma_ok, Ifma.scalarBase_ifma_ct, by lit_decide, by lit_decide⟩

end VG.Proof.Ed25519.X86_64

end

end

/-!
# Ed25519 public-key derivation on x86-64: pruning and the base point

The first half of the digest, pruned, is stored in the frame (`prune_ok`),
`[s]B` is encoded into `out` (`base_ok`), and the frame's copy of `s` is
cleared (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Arithmetic -/

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]; rfl
  rw [e, show (8 : Nat) = 2 ^ 3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow {y k : Nat} (h : y < 2 ^ k) : y ||| 2 ^ k = 2 ^ k + y := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [this, Nat.or_comm]

/-- The pruning of `Spec.Ed25519.prune`, on four 64-bit words. -/
theorem prune_words (d₀ d₁ d₂ d₃ : BitVec 64) :
    ((d₀.toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat + 2 ^ 192 * d₃.toNat) &&& (2 ^ 254 - 8)) |||
        2 ^ 254 =
      (d₀ &&& BitVec.ofNat 64 (2 ^ 64 - 8)).toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat +
        2 ^ 192 * ((d₃ &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)).toNat := by
  have h₀ := d₀.isLt; have h₁ := d₁.isLt; have h₂ := d₂.isLt; have h₃ := d₃.isLt
  have c₁ : (2 ^ 64 - 8) % 2 ^ 64 = 2 ^ 64 - 8 := by decide
  have c₂ : (2 ^ 62 - 1) % 2 ^ 64 = 2 ^ 62 - 1 := by decide
  have c₃ : (2 ^ 62) % 2 ^ 64 = 2 ^ 62 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 64 (by omega_using []), and_sub8 _ 254 (by omega_using []),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega_using [])), or_two_pow (by omega_using [])]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega_using []

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 48 (by omega_using []) (by omega_using [])).trans hc.pScr, (keep 56 (by omega_using []) (by omega_using [])).trans hc.pSeed,
    (keep 64 (by omega_using []) (by omega_using [])).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_using [])⟩), by rw [hsy]; exact hc.sym, hc.held⟩

/-- Word `k` of the digest. -/
abbrev dw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1568 + 8 * k)) 64

/-- The arguments of `vg_ed25519_scalar_base`. -/
def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have l48 := hc.inFr (d := 48) (by omega_using []) (by omega_using [])
  have l64 := hc.inFr (d := 64) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, l48, l64,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem pruneRegs_ok {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    WP isa (.block pkPruneRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' ∧
      t'.gpr .r8 = (dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = dw t L 1 ∧
      t'.gpr .r10 = dw t L 2 ∧
      t'.gpr .r11 = ((dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  obtain ⟨hdi, hsi, hdx⟩ := ha
  have s0 := hc.inScr (o := 1568) (by omega_using [])
  have s1 := hc.inScr (o := 1576) (by omega_using [])
  have s2 := hc.inScr (o := 1584) (by omega_using [])
  have s3 := hc.inScr (o := 1592) (by omega_using [])
  apply WP.of_runBlock
  simp only [pkPruneRegs, digestWord, digestAt, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, 
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hdx,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left', BaseArgs, hdi, hsi]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, ⟨trivial, trivial, trivial⟩,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-8)) = BitVec.ofNat 64 (2 ^ 64 - 8)),
    trivial, trivial, trivial⟩

/-- Four words stored in the frame's scalar. -/
theorem four_ok (B : Addr) (m : Mem) (a b c d : BitVec 64) :
    let m' := (((m.writeW (B + BitVec.ofNat 64 16) a).writeW (B + BitVec.ofNat 64 24) b).writeW
      (B + BitVec.ofNat 64 32) c).writeW (B + BitVec.ofNat 64 40) d
    Frame [⟨B + BitVec.ofNat 64 16, 32⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 16) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 24) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 32) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 40) 64 = d := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 72 → y + 8 ≤ 72 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega_using [h₁]) (by omega_using [h₂])
  have ct : ∀ x, 16 ≤ x → x + 8 ≤ 48 →
      (⟨B + BitVec.ofNat 64 16, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega_using [h₂]) (by omega_using [])
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 16 (by omega_using []) (by omega_using []))).writeW
    (List.mem_singleton_self _) _ (ct 24 (by omega_using []) (by omega_using []))).writeW (List.mem_singleton_self _) _
    (ct 32 (by omega_using []) (by omega_using []))).writeW (List.mem_singleton_self _) _ (ct 40 (by omega_using []) (by omega_using []))),
    ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 16 40 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep 16 32 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep 16 24 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 24 40 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep 24 32 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 32 40 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]

theorem stores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega_using []) (by omega_using [])
  have w1 := hc.inFrW (d := 24) (by omega_using []) (by omega_using [])
  have w2 := hc.inFrW (d := 32) (by omega_using []) (by omega_using [])
  have w3 := hc.inFrW (d := 40) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store rfl rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The number of four words in memory. -/
theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) = (m.readW p 64).toNat +
      2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      2 ^ 128 * (m.readW (p + BitVec.ofNat 64 16) 64).toNat +
      2 ^ 192 * (m.readW (p + BitVec.ofNat 64 24) 64).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words64 m p

theorem take_bytesAt (m : Mem) (p : Addr) :
    (Spec.Sha512.bytesAt m p 64).take 32 = Spec.Ed25519.bytesAt m p 32 := by
  simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.scr + BitVec.ofNat 64 1568) 64 = h) :
    WP isa (.block pkPrune) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧ BaseArgs L t' ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [pkPrune, WP.block_append_iff]
  refine WP.mono (pruneRegs_ok hc ha) fun u ⟨hcu, hmu, hau, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (stores_ok hcu) fun u' ⟨hcu', hf, hg, r0, r1, r2, r3⟩ => ?_
  refine ⟨hcu', hmu ▸ hf, by simp only [BaseArgs, hg]; exact hau, ?_⟩
  rw [Spec.Ed25519.prune, ← hh, take_bytesAt]
  simp only [decode_words, add_add, Nat.reduceAdd, r0, r1, r2, r3, h8, h9, h10, h11]
  exact (prune_words _ _ _ _).symm

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Both facts about every instruction of the base-point multiplication that
the calls need, in one evaluation of its code. -/
theorem base_instrs : bs.allInstrs
    (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true :=
  VG.Proof.Ed25519.X86_64.EdBase.instrs

theorem allInstrs_and {p q : Instr → Bool} {c : Prog isa}
    (h : c.allInstrs (fun i => p i && q i) = true) :
    c.allInstrs p = true ∧ c.allInstrs q = true := by
  simp only [Code.allInstrs_eq, List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩

theorem base_nosp : NoSp bs :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (allInstrs_and base_instrs).1

theorem base_depth : bs.depth ≤ 1 := VG.Proof.Ed25519.X86_64.EdBase.depth

/-- No instruction of the base-point multiplication writes `rsp`. -/
theorem base_spSafe : bs.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (allInstrs_and base_instrs).2

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 32⟩, L.TBL]
abbrev baseWr (L : Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

/-- The tables, as on entry, on entry to a call from the frame. -/
theorem ce_tbl (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {i : Nat} (hi : i < Impl.Ed25519.X86_64.combWordCount) :
    t.callEntry.mem.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  rw [← hc.held i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : L.T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b = L.TBL.base + BitVec.ofNat 64 (8 * i + b) := by
    rw [Offset.add_add]
  rw [e, ce_byte t (R := L.TBL) (by rw [hc.ret]; exact (hL.tbk.sub_right (Offset.sub_base _ (by omega_using []))).symm)
    (by show 8 * Impl.Ed25519.X86_64.combWordCount ≤ 2 ^ 64; decide) (by show 8 * i + b < 8 * Impl.Ed25519.X86_64.combWordCount; simp only [Impl.Ed25519.X86_64.combWordCount] at hi ⊢; omega_using [hi, hb])]
  exact Frame.bytes (R := L.TBL) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.tbo
    · exact hL.tbc
    · exact hL.tbk) (by show 8 * Impl.Ed25519.X86_64.combWordCount ≤ 2 ^ 64; decide) (by show 8 * i + b < 8 * Impl.Ed25519.X86_64.combWordCount; simp only [Impl.Ed25519.X86_64.combWordCount] at hi ⊢; omega_using [hi, hb])

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  have hsy : (t.callEntry.withRegions (baseRd L) (baseWr L)).syms combSym = L.T := hc.sym
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, Proof.Ed25519.X86_64.CombHeld, g1, g2, g3, rsp_ce,
    hc.rsp, sub8, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hsy]
  refine ⟨trivial, trivial, hL.stk_SCR (by omega_using []), hL.stk_OUT (by omega_using []), hL.stk_SCR (by omega_using []), hL.nc,
    fun i hi => ce_tbl hL hc hi, hL.nt, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.tbo
  · exact hL.tbc
  · exact hL.tbk.sub_right (Offset.sub_base _ (by omega_using []))

/-- The callee's buffers are apart from the 8 bytes below its `rsp`, the stack's lowest. -/
theorem base_clear (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    Clear (hole ((t.callEntry.withRegions (baseRd L) (baseWr L)).gpr .rsp))
      (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  rw [rsp_ce, hc.rsp, sub8, Proof.Ed25519.X86_64.hole_add8]
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact hL.tbk.sub_right (Region.sub_prefix (by omega_using []))
  · simpa using (hL.stk_OUT (d := 0) (n := 8) (by omega_using [])).symm
  · simpa using (hL.stk_SCR (d := 0) (n := 8) (by omega_using [])).symm

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ [L.SEED, L.TBL, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_stk _ (by omega_using []) (by omega_using [])⟩
  · exact ⟨L.TBL, by simp, within_base _ (by omega_using [])⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega_using [])⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega_using [])⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by omega_using []))
  · exact .inr (within_base _ (by omega_using []))

theorem base_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {s : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) = s) :
    WP isa (.call (scalarBaseName fs) bs) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint) := by
  refine call_ok hL (VG.Proof.Ed25519.X86_64.EdBase.ok (bs := bs)) base_nosp base_depth hc
    ⟨base_pre hL hc ha, base_clear hL hc⟩ base_sub base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Contract.clear, Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using []))
      (by show (32 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed25519.scalarBase, hs]

end VG.Proof.Ed25519.X86_64.PublicKey
