import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PublicKey.Layout`. -/
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

/-- The buffers and the lowest byte of the stack used (`rsp - 72` on entry). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  B : Addr

namespace Lay

variable (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay)

abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 72⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 56⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 72, 8⟩

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
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed25519.X86_64.PublicKey.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Ed25519.X86_64.PublicKey.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Ed25519.X86_64.PublicKey.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_stk (B : Addr) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 72) :
    VG.Proof.Ed25519.X86_64.PublicKey.Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 56⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_out (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 32) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ :=
  (h.ko.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_seed (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 32) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.seed + BitVec.ofNat 64 e, k⟩ :=
  (h.ks.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem seed_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.seed, 32⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.sc.sub_right (Offset.sub_base _ h₂)

theorem out_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.out, 32⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.oc.sub_right (Offset.sub_base _ h₂)

theorem stk_SEED (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SEED := h.ks.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  VG.Proof.Ed25519.X86_64.PublicKey.sub8 B

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
structure Ctx (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.SEED]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = L.scr
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 56) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 64) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

/-- A call of verified code (see `WP.call`), which nests calls at most once
more and is given regions within `seed`, the frame, `out` and `scratch` to
read and within `out` and `scratch` to write: afterwards `Ctx` holds again,
memory changed only within what it writes and the 16 bytes below `rsp`, and
the callee's postcondition holds. -/
theorem call_ok {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
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
      exact VG.Proof.Ed25519.X86_64.PublicKey.below_call_sub _ (by omega)
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
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
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

/-- The x86-64 contract of `vg_ed25519_public_key`: `Spec.Ed25519.publicKeyContract`
for 72 bytes of stack, spelled out (`out = rdi`, `seed = rsi`, `scratch = rdx`). -/
def pkLocal : Contract isa where
  pre s := 72 ≤ (s.gpr .rsp).toNat ∧ s.rd = [⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .rdi) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Ed25519.X86_64.PublicKey.Lay := ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rsp - BitVec.ofNat 64 72⟩

theorem lay_ret (s : State) : (VG.Proof.Ed25519.X86_64.PublicKey.lay s).B + BitVec.ofNat 64 72 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed25519.X86_64.PublicKey.lay s).Ok := by
  obtain ⟨-, -, -, os, oc, sc, ro, rs, rc, ko, ks, kc, no, ns, nc⟩ := h
  have e : (VG.Proof.Ed25519.X86_64.PublicKey.lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, VG.Proof.Ed25519.X86_64.PublicKey.lay_ret]
  exact ⟨os, oc, sc, ko, ks, kc, e ▸ ro, e ▸ rs, e ▸ rc, no, ns, nc⟩

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 public-key derivation on x86-64: the hash of the seed

From the state after the frame's push (`push_ctx`), the calls of `init`,
`update` and `finalize` leave `SHA-512(seed)` at `scratch + 1568` (`hash_ok`),
for any implementation `v` of the compression function.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed25519.X86_64.PublicKey.ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Ed25519.X86_64.PublicKey.ofInt_nat]

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

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.frame⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [VG.Proof.Ed25519.X86_64.PublicKey.sub8']

theorem ce_rsp (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) : t.callEntry.gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [State.callEntry_rsp, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.sub8]

/-- The seed, as on entry. -/
theorem seed (hL : L.Ok) (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {i : Nat} (hi : i < 32) :
    t.mem (L.seed + BitVec.ofNat 64 i) = m₀ (L.seed + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.SEED) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.os.symm
    · exact hL.sc
    · exact hL.ks.symm) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

/-- The seed on entry to a call from the frame. -/
theorem ce_seed (hL : L.Ok) (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    Spec.Ed25519.bytesAt t.callEntry.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 := by
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [VG.Proof.Ed25519.X86_64.PublicKey.ce_byte t (R := L.SEED) (by rw [hc.ret]; exact hL.stk_SEED (by omega)) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi]
  exact hc.seed hL hi

theorem inFr (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem ea_fr (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (d : Nat) : t.ea (stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [VG.Proof.Ed25519.X86_64.PublicKey.ea_stk, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.add_add]

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

theorem push_ctx {s : State} (h : pkLocal.pre s) :
    VG.Proof.Ed25519.X86_64.PublicKey.Ctx (VG.Proof.Ed25519.X86_64.PublicKey.lay s) s.gpr s.mxcsr s.mem (pushed VG.Proof.Ed25519.X86_64.PublicKey.pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Proof.Ed25519.X86_64.PublicKey.pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 3), (pushed VG.Proof.Ed25519.X86_64.PublicKey.pushRs s).mem.readW
      ((VG.Proof.Ed25519.X86_64.PublicKey.lay s).B + BitVec.ofNat 64 (64 - 8 * j)) 64 = s.gpr (VG.Proof.Ed25519.X86_64.PublicKey.pushRs[j]'(by show j < 7; omega)) := fun j hj => by
    rw [← hw j (by show j < 7; omega)]; simp only [VG.Proof.Ed25519.X86_64.PublicKey.lay]; rw [VG.Proof.Ed25519.X86_64.PublicKey.push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [List.length_cons, List.length_nil, VG.Proof.Ed25519.X86_64.PublicKey.lay]; rw [VG.Proof.Ed25519.X86_64.PublicKey.push_base]
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, VG.Proof.Ed25519.X86_64.PublicKey.lay]; rw [VG.Proof.Ed25519.X86_64.PublicKey.push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(VG.Proof.Ed25519.X86_64.PublicKey.lay s).STK, by simp, ?_⟩
    simp only [List.length_cons, List.length_nil]
    rw [VG.Proof.Ed25519.X86_64.PublicKey.push_base]
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
macro "cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- What the call of `init` needs of the registers. -/
def InitArgs (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (t : State) : Prop := t.gpr .rdi = L.scr

abbrev initRd : List Region := []
abbrev initWr (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region := [⟨L.scr, 192⟩]

theorem initArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkInitArgs) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.InitArgs L t' := by
  have hin := hc.inFr (d := 48) (by omega) (by omega)
  refine WP.of_runBlock ⟨t.setReg .rdi L.scr, ?_, ?_⟩
  · simp only [pkInitArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, hc.ea_fr, hin, ite_true, Option.map_some, hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ (VG.Proof.Ed25519.X86_64.PublicKey.ne_cs hr (by decide)), rfl,
    RegUpd.gpr_setReg_self _ _ _⟩

theorem init_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.InitArgs L t) :
    (Proof.Sha512.initX86_64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions VG.Proof.Ed25519.X86_64.PublicKey.initRd (VG.Proof.Ed25519.X86_64.PublicKey.initWr L)) := by
  have hrdi := (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce t VG.Proof.Ed25519.X86_64.PublicKey.initRd (VG.Proof.Ed25519.X86_64.PublicKey.initWr L) (r := .rdi) (by decide)).trans ha
  refine ⟨rfl, by rw [hrdi]; rfl, ?_⟩
  rw [VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, hrdi, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.sub8]
  simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega)

theorem init_sub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.initRd ++ VG.Proof.Ed25519.X86_64.PublicKey.initWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R := by
  simp only [List.nil_append, List.mem_singleton]
  rintro r rfl
  exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩

theorem init_wsub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.initWr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_singleton]
  rintro r rfl
  exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega))

theorem init_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.InitArgs L t) :
    WP isa (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] := by
  refine VG.Proof.Ed25519.X86_64.PublicKey.call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (VG.Proof.Ed25519.X86_64.PublicKey.nosp_init _) (by decide) hc
    (VG.Proof.Ed25519.X86_64.PublicKey.init_pre hL hc ha) VG.Proof.Ed25519.X86_64.PublicKey.init_sub VG.Proof.Ed25519.X86_64.PublicKey.init_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  have := hpost
  simp only [Proof.Sha512.initX86_64, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce t VG.Proof.Ed25519.X86_64.PublicKey.initRd (VG.Proof.Ed25519.X86_64.PublicKey.initWr L) (r := .rdi) (by decide)).trans ha] at this
  rwa [← hm]

theorem init_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (callWith pkInitArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] :=
  WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.initArgs_ok hc) fun _ ⟨hc₁, _, ha⟩ => VG.Proof.Ed25519.X86_64.PublicKey.init_call hL hc₁ ha)

/-! ## `update` and `finalize`, for any compression function -/

/-- SHA-512 with the compression function `v`, as `MdHash` builds it. -/
abbrev hashOf (v : Compress) : Impl.Pbkdf2.Md.X86_64.Hash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name
    Spec.Sha512.H0_512 v

theorem callees (v : Compress) : Proof.Pbkdf2.Md.X86_64.Callees (VG.Proof.Ed25519.X86_64.PublicKey.hashOf v) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.callees (Or.inr (Or.inl rfl)) v

theorem coreOK (v : Compress) : Proof.Pbkdf2.Md.X86_64.CoreOK (Proof.Pbkdf2.Md.X86_64.core (VG.Proof.Ed25519.X86_64.PublicKey.hashOf v)) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_coreOK

theorem upd_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.update v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).updMx (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem fin_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).finMx (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem upd_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.update v.callee) :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).updSp (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem fin_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.finalize v.callee) :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).finSp (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem upd_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.update v.callee).depth ≤ 1 :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).updD (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem fin_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.finalize v.callee).depth ≤ 1 :=
  (VG.Proof.Ed25519.X86_64.PublicKey.callees v).finD (VG.Proof.Ed25519.X86_64.PublicKey.coreOK v)

theorem upd_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update v.callee) Proof.Sha512.updateX86_64 :=
  Proof.Sha512.X86_64.Stream.Update.verified_of v.ok (VG.Proof.Ed25519.X86_64.PublicKey.upd_mx v)

theorem fin_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalize v.callee) Proof.Sha512.finalizeX86_64 :=
  Proof.Sha512.X86_64.Stream.Finalize.verified_of v.ok (VG.Proof.Ed25519.X86_64.PublicKey.fin_mx v)

theorem cs_keep {t : State} {d : Reg} (v : BitVec 64) (hd : d ∉ calleeSaved) :
    ∀ r ∈ calleeSaved, (t.setReg d v).gpr r = t.gpr r :=
  fun _ hr => RegUpd.gpr_setReg_of_ne _ _ (VG.Proof.Ed25519.X86_64.PublicKey.ne_cs hr hd)

/-- What the call of `update` needs of the registers. -/
def UpdArgs (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = 0 ∧ t.gpr .rdx = L.seed ∧ t.gpr .rcx = BitVec.ofNat 64 32 ∧
    t.gpr .r8 = L.scr + BitVec.ofNat 64 192

theorem updArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkUpdateArgs) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs L t' := by
  have h48 := hc.inFr (d := 48) (by omega) (by omega)
  have h56 := hc.inFr (d := 56) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkUpdateArgs, scrPtr, shaScratch, fScratch, fSeed, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, VG.Proof.Ed25519.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.add_add,
    Nat.reduceAdd, h48, h56, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSeed, VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl, trivial, rfl, by rw [VG.Proof.Ed25519.X86_64.PublicKey.sx32 (by omega)]⟩

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- The state at `scratch`, on entry to a call from the frame. -/
theorem Ctx.ce_repr (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {iv : Spec.Sha512.HashValue}
    {m : List Byte} (hr : Spec.Sha512.Repr iv t.mem L.scr m) : Spec.Sha512.Repr iv t.callEntry.mem L.scr m :=
  Proof.Sha512.Stream.repr_congr (fun i hi => VG.Proof.Ed25519.X86_64.PublicKey.ce_byte t (R := ⟨L.scr, 192⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega))
    (by show (192 : Nat) ≤ 2 ^ 64; decide) hi) hr

abbrev updRd (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region := [L.SEED]
abbrev updWr (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region := [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem upd_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧ (t.callEntry.withRegions rd wr).gpr .rsi = 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.seed ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = BitVec.ofNat 64 32 ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = L.scr + BitVec.ofNat 64 192 :=
  ⟨(VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem upd_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs L t) :
    Proof.Sha512.updateX86_64.pre (t.callEntry.withRegions (VG.Proof.Ed25519.X86_64.PublicKey.updRd L) (VG.Proof.Ed25519.X86_64.PublicKey.updWr L)) := by
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := VG.Proof.Ed25519.X86_64.PublicKey.upd_regs ha (VG.Proof.Ed25519.X86_64.PublicKey.updRd L) (VG.Proof.Ed25519.X86_64.PublicKey.updWr L)
  simp only [Proof.Sha512.updateX86_64, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, hdi, hdx, hcx, h8, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.sub8, VG.Proof.Ed25519.X86_64.PublicKey.sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by trivial, by trivial, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.seed_scr (e := 0) (k := 192) (by omega), hL.seed_scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hL.stk_SEED (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem upd_sub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.updRd L ++ VG.Proof.Ed25519.X86_64.PublicKey.updWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SEED, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega)⟩

theorem upd_wsub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.updWr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega))

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs L t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine VG.Proof.Ed25519.X86_64.PublicKey.call_ok hL (VG.Proof.Ed25519.X86_64.PublicKey.upd_verified v).1 (VG.Proof.Ed25519.X86_64.PublicKey.upd_nosp v) (VG.Proof.Ed25519.X86_64.PublicKey.upd_depth v) hc (VG.Proof.Ed25519.X86_64.PublicKey.upd_pre hL hc ha) VG.Proof.Ed25519.X86_64.PublicKey.upd_sub VG.Proof.Ed25519.X86_64.PublicKey.upd_wsub
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, -⟩ := VG.Proof.Ed25519.X86_64.PublicKey.upd_regs ha (VG.Proof.Ed25519.X86_64.PublicKey.updRd L) (VG.Proof.Ed25519.X86_64.PublicKey.updWr L)
  have h := hpost Spec.Sha512.H0_512 []
    (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (by rw [hsi]; rfl)
  simp only [State.withRegions_mem, hdi, hdx, hcx, List.nil_append, hm] at h
  have e : Spec.Sha512.bytesAt t.callEntry.mem L.seed (BitVec.ofNat 64 32).toNat =
      Spec.Ed25519.bytesAt m₀ L.seed 32 := hc.ce_seed hL
  rwa [e] at h

theorem upd_step (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (callWith pkUpdateArgs (Spec.Sha512.updateScratchApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.updArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => VG.Proof.Ed25519.X86_64.PublicKey.upd_call v hL hc₁ ha (hm₁ ▸ hr))

/-- What the call of `finalize` needs of the registers. -/
def FinArgs (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 32 ∧ t.gpr .rdx = L.scr + BitVec.ofNat 64 1568 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 192

theorem finArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkFinalizeArgs) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.FinArgs L t' := by
  have h48 := hc.inFr (d := 48) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkFinalizeArgs, scrPtr, shaScratch, digestAt, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, VG.Proof.Ed25519.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.add_add,
    Nat.reduceAdd, h48, Option.some.injEq, exists_eq_left', hc.pScr, VG.Proof.Ed25519.X86_64.PublicKey.FinArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl, by rw [VG.Proof.Ed25519.X86_64.PublicKey.sx32 (by omega)],
    by rw [VG.Proof.Ed25519.X86_64.PublicKey.sx32 (by omega)]⟩

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp [Spec.Ed25519.bytesAt]

abbrev finRd : List Region := []
abbrev finWr (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 1568, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.PublicKey.FinArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 32 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr + BitVec.ofNat 64 1568 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.scr + BitVec.ofNat 64 192 :=
  ⟨(VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.FinArgs L t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions VG.Proof.Ed25519.X86_64.PublicKey.finRd (VG.Proof.Ed25519.X86_64.PublicKey.finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := VG.Proof.Ed25519.X86_64.PublicKey.fin_regs ha VG.Proof.Ed25519.X86_64.PublicKey.finRd (VG.Proof.Ed25519.X86_64.PublicKey.finWr L)
  simp only [Proof.Sha512.finalizeX86_64, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, hdi, hdx, hcx, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.sub8, VG.Proof.Ed25519.X86_64.PublicKey.sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by trivial, by trivial, Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega), Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 1568) (k := 64) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem fin_sub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.finRd ++ VG.Proof.Ed25519.X86_64.PublicKey.finWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega)⟩

theorem fin_wsub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.finWr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega))
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_off _ (by omega))

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.FinArgs L t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (.call (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine VG.Proof.Ed25519.X86_64.PublicKey.call_ok hL (VG.Proof.Ed25519.X86_64.PublicKey.fin_verified v).1 (VG.Proof.Ed25519.X86_64.PublicKey.fin_nosp v) (VG.Proof.Ed25519.X86_64.PublicKey.fin_depth v) hc (VG.Proof.Ed25519.X86_64.PublicKey.fin_pre hL hc ha) VG.Proof.Ed25519.X86_64.PublicKey.fin_sub VG.Proof.Ed25519.X86_64.PublicKey.fin_wsub
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, -⟩ := VG.Proof.Ed25519.X86_64.PublicKey.fin_regs ha VG.Proof.Ed25519.X86_64.PublicKey.finRd (VG.Proof.Ed25519.X86_64.PublicKey.finWr L)
  have h := hpost Spec.Sha512.H0_512 (Spec.Ed25519.bytesAt m₀ L.seed 32)
    (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr)
    (by rw [VG.Proof.Ed25519.X86_64.PublicKey.bytesAt_length]; decide) (by rw [hsi, VG.Proof.Ed25519.X86_64.PublicKey.bytesAt_length])
  rw [hdx, hm] at h
  exact h

theorem fin_step (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (callWith pkFinalizeArgs (Spec.Sha512.finalizeScratchApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.finArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => VG.Proof.Ed25519.X86_64.PublicKey.fin_call v hL hc₁ ha (hm₁ ▸ hr))

end VG.Proof.Ed25519.X86_64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base`. -/
section

/-!
# Ed25519 public-key derivation on x86-64: pruning and the base point

The first half of the digest, pruned, is stored in the frame (`prune_ok`),
`[s]B` is encoded into `out` (`base_ok`), and the frame's copy of `s` is
cleared (`wipe_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

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
    BitVec.toNat_ofNat, c₁, c₂, c₃, VG.Proof.Ed25519.X86_64.PublicKey.and_sub8 _ 64 (by omega), VG.Proof.Ed25519.X86_64.PublicKey.and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, VG.Proof.Ed25519.X86_64.PublicKey.or_two_pow (Nat.mod_lt _ (by omega)), VG.Proof.Ed25519.X86_64.PublicKey.or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem) : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' := by
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 48 (by omega) (by omega)).trans hc.pScr, (keep 56 (by omega) (by omega)).trans hc.pSeed,
    (keep 64 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩)⟩

/-- Word `k` of the digest. -/
abbrev dw (t : State) (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1568 + 8 * k)) 64

/-- The arguments of `vg_ed25519_scalar_base`. -/
def BaseArgs (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t' := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, VG.Proof.Ed25519.X86_64.PublicKey.ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.add_add, Nat.reduceAdd, l48, l64,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem pruneRegs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t) :
    WP isa (.block pkPruneRegs) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t' ∧
      t'.gpr .r8 = (VG.Proof.Ed25519.X86_64.PublicKey.dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = VG.Proof.Ed25519.X86_64.PublicKey.dw t L 1 ∧
      t'.gpr .r10 = VG.Proof.Ed25519.X86_64.PublicKey.dw t L 2 ∧
      t'.gpr .r11 = ((VG.Proof.Ed25519.X86_64.PublicKey.dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  obtain ⟨hdi, hsi, hdx⟩ := ha
  have s0 := hc.inScr (o := 1568) (by omega)
  have s1 := hc.inScr (o := 1576) (by omega)
  have s2 := hc.inScr (o := 1584) (by omega)
  have s3 := hc.inScr (o := 1592) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneRegs, digestWord, digestAt, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, VG.Proof.Ed25519.X86_64.PublicKey.ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hdx,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left', VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs, hdi, hsi]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, ⟨trivial, trivial, trivial⟩,
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
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 16 ≤ x → x + 8 ≤ 48 →
      (⟨B + BitVec.ofNat 64 16, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 16 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 24 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 32 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 40 (by omega) (by omega))),
    ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 16 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 16 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 16 24 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 24 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 32 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]

theorem stores_ok {u : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega) (by omega)
  have w1 := hc.inFrW (d := 24) (by omega) (by omega)
  have w2 := hc.inFrW (d := 32) (by omega) (by omega)
  have w3 := hc.inFrW (d := 40) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    VG.Proof.Ed25519.X86_64.PublicKey.ea_stk, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := VG.Proof.Ed25519.X86_64.PublicKey.four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

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

theorem prune_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.scr + BitVec.ofNat 64 1568) 64 = h) :
    WP isa (.block pkPrune) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧ VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t' ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [pkPrune, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.pruneRegs_ok hc ha) fun u ⟨hcu, hmu, hau, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.stores_ok hcu) fun u' ⟨hcu', hf, hg, r0, r1, r2, r3⟩ => ?_
  refine ⟨hcu', hmu ▸ hf, by simp only [VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs, hg]; exact hau, ?_⟩
  rw [Spec.Ed25519.prune, ← hh, VG.Proof.Ed25519.X86_64.PublicKey.take_bytesAt]
  simp only [VG.Proof.Ed25519.X86_64.PublicKey.decode_words, VG.Proof.Ed25519.X86_64.PublicKey.add_add, Nat.reduceAdd, r0, r1, r2, r3, h8, h9, h10, h11]
  exact (VG.Proof.Ed25519.X86_64.PublicKey.prune_words _ _ _ _).symm

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Both facts about every instruction of the base-point multiplication that
the calls need, in one evaluation of its code. -/
theorem base_instrs : (scalarBase_precomputed fld).allInstrs
    (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true := by
  fld_lit_decide

theorem allInstrs_and {p q : Instr → Bool} {c : Prog isa}
    (h : c.allInstrs (fun i => p i && q i) = true) :
    c.allInstrs p = true ∧ c.allInstrs q = true := by
  simp only [Code.allInstrs_eq, List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩

theorem base_nosp : NoSp (scalarBase_precomputed fld) :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Ed25519.X86_64.PublicKey.allInstrs_and VG.Proof.Ed25519.X86_64.PublicKey.base_instrs).1

theorem base_depth : (scalarBase_precomputed fld).depth ≤ 1 := by fld_lit_decide

/-- No instruction of the base-point multiplication writes `rsp`. -/
theorem base_spSafe : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (VG.Proof.Ed25519.X86_64.PublicKey.allInstrs_and VG.Proof.Ed25519.X86_64.PublicKey.base_instrs).2

abbrev baseRd (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 32⟩]
abbrev baseWr (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.1, (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (VG.Proof.Ed25519.X86_64.PublicKey.baseRd L) (VG.Proof.Ed25519.X86_64.PublicKey.baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := VG.Proof.Ed25519.X86_64.PublicKey.base_regs ha (VG.Proof.Ed25519.X86_64.PublicKey.baseRd L) (VG.Proof.Ed25519.X86_64.PublicKey.baseWr L)
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, g3, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, hc.rsp, VG.Proof.Ed25519.X86_64.PublicKey.sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.nc⟩

theorem base_sub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.baseRd L ++ VG.Proof.Ed25519.X86_64.PublicKey.baseWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_stk _ (by omega) (by omega)⟩
  · exact ⟨L.OUT, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ VG.Proof.Ed25519.X86_64.PublicKey.baseWr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega))
  · exact .inr (VG.Proof.Ed25519.X86_64.PublicKey.within_base _ (by omega))

theorem base_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs L t) {s : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) = s) :
    WP isa (.call (scalarBaseName fs) (scalarBase_precomputed fld)) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint) := by
  refine VG.Proof.Ed25519.X86_64.PublicKey.call_ok hL Proof.Ed25519.X86_64.scalarBase_precomputed_ok VG.Proof.Ed25519.X86_64.PublicKey.base_nosp VG.Proof.Ed25519.X86_64.PublicKey.base_depth hc
    (VG.Proof.Ed25519.X86_64.PublicKey.base_pre hL hc ha) VG.Proof.Ed25519.X86_64.PublicKey.base_sub VG.Proof.Ed25519.X86_64.PublicKey.base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := VG.Proof.Ed25519.X86_64.PublicKey.base_regs ha (VG.Proof.Ed25519.X86_64.PublicKey.baseRd L) (VG.Proof.Ed25519.X86_64.PublicKey.baseWr L)
  have h := hpost
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact VG.Proof.Ed25519.X86_64.PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by show (32 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed25519.scalarBase, hs]

end VG.Proof.Ed25519.X86_64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.PublicKey.Correct`. -/
section
/-!
# Ed25519 public-key derivation on x86-64: correctness

The frame's body leaves the public key in `out` (`body_ok`), and the whole
function, for any implementation `v` of the SHA-512 compression function,
meets `pkLocal` and the ABI (`publicKey_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

variable {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem zero_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkZero) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkZero, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.zero_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.stores_ok hu) fun u' ⟨hu', hf, _⟩ => ⟨hu', hm ▸ hf⟩

/-- `SHA-512(seed)` at `scratch + 1568`. -/
theorem hash_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (pkHash v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.init_step hL hc) fun _ ⟨hc₁, hr₁⟩ =>
    WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.upd_step v hL hc₁ hr₁) fun _ ⟨hc₂, hr₂⟩ => VG.Proof.Ed25519.X86_64.PublicKey.fin_step v hL hc₂ hr₂))

/-- The public key of the seed in `out`. -/
theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) :
    WP isa (pkBody fld fs v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.hash_ok v hL hc) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.baseArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.prune_ok hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, _, ha₃, hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.base_ok hL hc₃ ha₃ hs) fun t₃ ⟨hc₃, ho₃⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.wipe_ok hc₃) fun t₄ ⟨hc₄, hf₄⟩ => ⟨hc₄, ?_⟩
  rw [Spec.Ed25519.publicKey, Spec.Ed25519.expandSecret, ← ho₃]
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact Frame.bytes (R := L.OUT) hf₄ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_OUT (d := 16) (n := 32) (by omega)).symm) (by show (32 : Nat) ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 7) = B + BitVec.ofNat 64 72 := by
  rw [VG.Proof.Ed25519.X86_64.PublicKey.add_add]

/-- `vg_ed25519_public_key` meets `pkLocal` and the ABI. -/
theorem publicKey_ok (v : Compress) {s : State} (h : pkLocal.pre s) :
    WP isa (publicKey fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ pkLocal.post s s' := by
  have hL := VG.Proof.Ed25519.X86_64.PublicKey.lay_ok h
  have hc := VG.Proof.Ed25519.X86_64.PublicKey.push_ctx h
  refine WP.frame (rs := VG.Proof.Ed25519.X86_64.PublicKey.pushRs) (by decide) (by decide) (by decide) (by show 8 * 7 ≤ _; have := h.1; omega)
    (WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.body_ok v hL hc) fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 7 from rfl, VG.Proof.Ed25519.X86_64.PublicKey.pop_rsp, VG.Proof.Ed25519.X86_64.PublicKey.lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (VG.Proof.Ed25519.X86_64.PublicKey.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (VG.Proof.Ed25519.X86_64.PublicKey.lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, VG.Proof.Ed25519.X86_64.PublicKey.lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (VG.Proof.Ed25519.X86_64.PublicKey.lay s).out 32 = _
    rw [popped_mem, ho]
    rfl

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 public-key derivation on x86-64: constant time

Two runs whose pointers agree have the same layout, so between the frame's
push and pop they are related by `Two`: both satisfy `Ctx` with that layout
(and `Φ`, what the next call needs of the registers), whatever their secrets.
The blocks address only the stack and, in `pkPrune`, `scratch`, from registers
that agree (the taint analysis); each call is of constant-time code whose
public data, its pointers, agree (`RelCT.callEx`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Two.Env := VG.Proof.Ed25519.X86_64.PublicKey.Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ VG.Proof.Ed25519.X86_64.PublicKey.Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧
    VG.Proof.Ed25519.X86_64.PublicKey.Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧ Φ e.1 a ∧ Φ e.1 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop}
    (hct : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      WP isa c t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) c (VG.Proof.Ed25519.X86_64.PublicKey.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_block {is : List Instr} {Φ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rsp_two {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {mx₁ mx₂ : BitVec 32} {m₁ m₂ : Mem}
    (c₁ : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁) (c₂ : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

theorem covers {L : VG.Proof.Ed25519.X86_64.PublicKey.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R)
    (hwsub : ∀ r ∈ wr, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call, with the same regions in both runs. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Ed25519.X86_64.PublicKey.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR) :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂, (VG.Proof.Ed25519.X86_64.PublicKey.covers c₁ (hsub L) (hwsub L)).1, (VG.Proof.Ed25519.X86_64.PublicKey.covers c₁ (hsub L) (hwsub L)).2,
      (VG.Proof.Ed25519.X86_64.PublicKey.covers c₂ (hsub L) (hwsub L)).1, (VG.Proof.Ed25519.X86_64.PublicKey.covers c₂ (hsub L) (hwsub L)).2, VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂⟩

/-- A block, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      WP isa (.block is) t fun t' => VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) (.block is) (VG.Proof.Ed25519.X86_64.PublicKey.Two Ψ) :=
  VG.Proof.Ed25519.X86_64.PublicKey.two_wp (VG.Proof.Ed25519.X86_64.PublicKey.two_block rs hrs h) hw

/-- A call of verified code, after which `Ctx` holds again. -/
theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : VG.Proof.Ed25519.X86_64.PublicKey.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], VG.Proof.Ed25519.X86_64.PublicKey.Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, VG.Proof.Ed25519.X86_64.PublicKey.Within r L.OUT ∨ VG.Proof.Ed25519.X86_64.PublicKey.Within r L.SCR) :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two Φ) (.call n c) (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) :=
  VG.Proof.Ed25519.X86_64.PublicKey.two_wp (VG.Proof.Ed25519.X86_64.PublicKey.two_call hv hct rd wr hpre hpub hsub hwsub) fun L _ _ _ _ hL hc hf =>
    VG.Proof.Ed25519.X86_64.PublicKey.call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (hsub L) (hwsub L) fun _ hc' _ _ _ => ⟨hc', trivial⟩

theorem rspOnly {Φ : VG.Proof.Ed25519.X86_64.PublicKey.Lay → State → Prop} : ∀ (L : VG.Proof.Ed25519.X86_64.PublicKey.Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.PublicKey.Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂

/-- The frame's body, for any implementation `v` of the compression function. -/
theorem body_ct (v : Compress) :
    RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (pkBody fld fs v.callee v.suffix) fun _ _ => True := by
  -- `init`
  have i₁ : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (.block pkInitArgs) (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.InitArgs) :=
    VG.Proof.Ed25519.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed25519.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have i₂ := VG.Proof.Ed25519.X86_64.PublicKey.two_callP (n := Spec.Sha512.init512Api.name) (Φ := VG.Proof.Ed25519.X86_64.PublicKey.InitArgs)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (VG.Proof.Ed25519.X86_64.PublicKey.nosp_init _) (by decide) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.initRd) VG.Proof.Ed25519.X86_64.PublicKey.initWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.PublicKey.init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce t₁ VG.Proof.Ed25519.X86_64.PublicKey.initRd (VG.Proof.Ed25519.X86_64.PublicKey.initWr L) (by decide)).trans a₁).trans
        ((VG.Proof.Ed25519.X86_64.PublicKey.gpr_ce t₂ VG.Proof.Ed25519.X86_64.PublicKey.initRd (VG.Proof.Ed25519.X86_64.PublicKey.initWr L) (by decide)).trans a₂).symm)
    (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.init_sub) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.init_wsub)
  -- `update`
  have u₁ : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (.block pkUpdateArgs) (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs) :=
    VG.Proof.Ed25519.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed25519.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.updArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have u₂ := VG.Proof.Ed25519.X86_64.PublicKey.two_callP (n := Spec.Sha512.updateScratchApi.name ++ v.suffix) (Φ := VG.Proof.Ed25519.X86_64.PublicKey.UpdArgs)
    (VG.Proof.Ed25519.X86_64.PublicKey.upd_verified v).1 (VG.Proof.Ed25519.X86_64.PublicKey.upd_verified v).2.1 (VG.Proof.Ed25519.X86_64.PublicKey.upd_nosp v) (VG.Proof.Ed25519.X86_64.PublicKey.upd_depth v) VG.Proof.Ed25519.X86_64.PublicKey.updRd VG.Proof.Ed25519.X86_64.PublicKey.updWr
    (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.PublicKey.upd_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := VG.Proof.Ed25519.X86_64.PublicKey.upd_regs a₁ (VG.Proof.Ed25519.X86_64.PublicKey.updRd L) (VG.Proof.Ed25519.X86_64.PublicKey.updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := VG.Proof.Ed25519.X86_64.PublicKey.upd_regs a₂ (VG.Proof.Ed25519.X86_64.PublicKey.updRd L) (VG.Proof.Ed25519.X86_64.PublicKey.updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂]⟩)
    (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.upd_sub) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.upd_wsub)
  -- `finalize`
  have f₁ : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (.block pkFinalizeArgs) (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.FinArgs) :=
    VG.Proof.Ed25519.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed25519.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.finArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have f₂ := VG.Proof.Ed25519.X86_64.PublicKey.two_callP (n := Spec.Sha512.finalizeScratchApi.name ++ v.suffix) (Φ := VG.Proof.Ed25519.X86_64.PublicKey.FinArgs)
    (VG.Proof.Ed25519.X86_64.PublicKey.fin_verified v).1 (VG.Proof.Ed25519.X86_64.PublicKey.fin_verified v).2.1 (VG.Proof.Ed25519.X86_64.PublicKey.fin_nosp v) (VG.Proof.Ed25519.X86_64.PublicKey.fin_depth v) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.finRd) VG.Proof.Ed25519.X86_64.PublicKey.finWr
    (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.PublicKey.fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := VG.Proof.Ed25519.X86_64.PublicKey.fin_regs a₁ VG.Proof.Ed25519.X86_64.PublicKey.finRd (VG.Proof.Ed25519.X86_64.PublicKey.finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := VG.Proof.Ed25519.X86_64.PublicKey.fin_regs a₂ VG.Proof.Ed25519.X86_64.PublicKey.finRd (VG.Proof.Ed25519.X86_64.PublicKey.finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂]⟩)
    (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.fin_sub) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.fin_wsub)
  -- the scalar and the base point
  have b₁ : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (.block pkBaseArgs) (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs) :=
    VG.Proof.Ed25519.X86_64.PublicKey.two_blk [.rsp] VG.Proof.Ed25519.X86_64.PublicKey.rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs) (.block pkPrune) (VG.Proof.Ed25519.X86_64.PublicKey.Two VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs) := by
    refine VG.Proof.Ed25519.X86_64.PublicKey.two_blk [.rsp, .rdx] (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ r hr => ?_) (by taint_decide)
      fun _ _ _ _ _ _ hc ha => WP.mono (VG.Proof.Ed25519.X86_64.PublicKey.prune_ok hc ha rfl) fun _ ⟨hc', _, ha', _⟩ => ⟨hc', ha'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂
    · exact a₁.2.2.trans a₂.2.2.symm
  have b₃ := VG.Proof.Ed25519.X86_64.PublicKey.two_callP (n := (scalarBaseName fs)) (Φ := VG.Proof.Ed25519.X86_64.PublicKey.BaseArgs)
    (Proof.Ed25519.X86_64.scalarBase_precomputed_ok (fld := fld)) (Proof.Ed25519.X86_64.scalarBase_precomputed_ct (fld := fld))
    VG.Proof.Ed25519.X86_64.PublicKey.base_nosp VG.Proof.Ed25519.X86_64.PublicKey.base_depth VG.Proof.Ed25519.X86_64.PublicKey.baseRd VG.Proof.Ed25519.X86_64.PublicKey.baseWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.PublicKey.base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := VG.Proof.Ed25519.X86_64.PublicKey.base_regs a₁ (VG.Proof.Ed25519.X86_64.PublicKey.baseRd L) (VG.Proof.Ed25519.X86_64.PublicKey.baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := VG.Proof.Ed25519.X86_64.PublicKey.base_regs a₂ (VG.Proof.Ed25519.X86_64.PublicKey.baseRd L) (VG.Proof.Ed25519.X86_64.PublicKey.baseWr L)
      exact ⟨by rw [VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_ce, VG.Proof.Ed25519.X86_64.PublicKey.rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.base_sub) (fun _ => VG.Proof.Ed25519.X86_64.PublicKey.base_wsub)
  have w : RelCT isa (VG.Proof.Ed25519.X86_64.PublicKey.Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    VG.Proof.Ed25519.X86_64.PublicKey.two_block [.rsp] VG.Proof.Ed25519.X86_64.PublicKey.rspOnly (by taint_decide)
  exact ((i₁.seq i₂).seq ((u₁.seq u₂).seq (f₁.seq f₂))).seq (b₁.seq (b₂.seq (b₃.seq w)))

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 public-key derivation on x86-64: the shared contract

`vg_ed25519_public_key`, made with any implementation `v` of the SHA-512
compression function, is verified against `Spec.Ed25519.publicKeyContract` for
the 72 bytes of stack its frame and calls use.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

theorem publicKey_ct (v : Compress) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKey fld fs v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1) (RelCT.mono (VG.Proof.Ed25519.X86_64.PublicKey.body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx⟩, rfl, rfl⟩
  have e : VG.Proof.Ed25519.X86_64.PublicKey.lay s₂ = VG.Proof.Ed25519.X86_64.PublicKey.lay s₁ := by simp only [VG.Proof.Ed25519.X86_64.PublicKey.lay, hsp, hdi, hsi, hdx]
  exact ⟨⟨VG.Proof.Ed25519.X86_64.PublicKey.lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, VG.Proof.Ed25519.X86_64.PublicKey.lay_ok h₁, VG.Proof.Ed25519.X86_64.PublicKey.push_ctx h₁,
    e ▸ VG.Proof.Ed25519.X86_64.PublicKey.push_ctx h₂, trivial, trivial⟩

theorem implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract X86_64.abi 72) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords,
    X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.PublicKey.pkLocal] [Proof.Ed25519.X86_64.baseSatState]
    using Proof.Ed25519.X86_64.baseSatState

theorem publicKey_verified (v : Compress) :
    Verified X86_64.target (publicKey fld fs v.callee v.suffix) (Spec.Ed25519.publicKeyContract X86_64.abi 72) :=
  Verified.of_correct (fun _ h => VG.Proof.Ed25519.X86_64.PublicKey.publicKey_ok v h) (VG.Proof.Ed25519.X86_64.PublicKey.publicKey_ct v) VG.Proof.Ed25519.X86_64.PublicKey.implies

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem publicKey_spSafe (v : Compress) :
    (publicKey fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hb : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true := VG.Proof.Ed25519.X86_64.PublicKey.base_spSafe
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [publicKey, pkBody, pkHash, callWith, Code.all, hu, hf, hb, hi, Bool.and_true, Bool.true_and]
  decide

end VG.Proof.Ed25519.X86_64.PublicKey

end
