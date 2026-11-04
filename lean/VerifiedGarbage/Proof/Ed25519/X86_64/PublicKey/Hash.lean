module

public import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86_64.Exec

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
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : Lay}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_out (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 32) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ :=
  (h.ko.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem out_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.out, 32⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.oc.sub_right (Offset.sub_base _ h₂)

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
  exact Offset.sub_base _ (by omega)

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
  refine WP.of_syms (WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx hsy => ?_)
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
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 48 (by omega) (by omega)).trans hc.pScr,
    (keep 56 (by omega) (by omega)).trans hc.pSeed, (keep 64 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_), hsy.symm ▸ hc.sym, hc.held⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact ⟨_, by simp, h.sub⟩
      · exact ⟨_, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 72) (by omega)
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

theorem ce_rsp (hc : Ctx L g mx m₀ t) : t.callEntry.gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [State.callEntry_rsp, hc.rsp, sub8]

theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem ea_fr (hc : Ctx L g mx m₀ t) (d : Nat) : t.ea (stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [ea_stk, hc.rsp, add_add]

end Ctx

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 7) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 3) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 (64 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem pushed_syms_eq (s : State) (rs : List Reg) : (pushed rs s).syms = s.syms := pushRegs_syms s rs

theorem push_ctx {n : Nat} {key : State → Prop} {post : State → State → Prop} {s : State}
    (h : (pkLocalWith n key post).pre s) :
    Ctx (lay n s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 3), (pushed pushRs s).mem.readW
      ((lay n s).B + BitVec.ofNat 64 (64 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 7; omega)) := fun j hj => by
    rw [← hw j (by show j < 7; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_, congrFun (pushed_syms_eq s pushRs) combSym,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · rw [pushed_wr, h.2.2.1]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay n s).STK, by simp, ?_⟩
    simp only [List.length_cons, List.length_nil]
    rw [push_base]
    exact Offset.sub_base _ (by omega)

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
  Proof.Pbkdf2.Md.X86_64.Sha512.hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name
    Spec.Sha512.H0_512 v

theorem callees (v : Compress) : Proof.Pbkdf2.Md.X86_64.Callees (hashOf v) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.callees (Or.inr (Or.inl rfl)) v

theorem coreOK (v : Compress) : Proof.Pbkdf2.Md.X86_64.CoreOK (Proof.Pbkdf2.Md.X86_64.core (hashOf v)) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_coreOK

theorem upd_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.update v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).updMx (coreOK v)

theorem fin_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).finMx (coreOK v)

theorem upd_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.update v.callee) :=
  (callees v).updSp (coreOK v)

theorem fin_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.finalize v.callee) :=
  (callees v).finSp (coreOK v)

theorem upd_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.update v.callee).depth ≤ 1 :=
  (callees v).updD (coreOK v)

theorem fin_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.finalize v.callee).depth ≤ 1 :=
  (callees v).finD (coreOK v)

theorem upd_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update v.callee) Proof.Sha512.updateX86_64 :=
  Proof.Sha512.X86_64.Stream.Update.verified_of v.ok (upd_mx v)

theorem fin_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalize v.callee) Proof.Sha512.finalizeX86_64 :=
  Proof.Sha512.X86_64.Stream.Finalize.verified_of v.ok (fin_mx v)

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.X86_64.PublicKey




