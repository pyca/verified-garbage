module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCT
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the test of a TLS record's text

Untrusted: everything here is checked by Lean. What `tlsTest long fill` computes
from the public lengths (`tlsGo`), in one run (`tlsTest_wp`) and in two runs
with the same public arguments (`tlsTest_rel`, which take the same path:
`Pub.eTls`). The test only chooses between paths that are correct for any
text, so `tlsGo` is what the code computes, not a statement of it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.AesGcm.X86_64 (rel_block_split)

/-- A `cmov`'s state, with the write folded into the register's value. -/
theorem ite_setReg (c : Prop) [Decidable c] (s : State) (r : Reg) (v : BitVec 64) :
    (if c then s.setReg r v else s) = s.setReg r (if c then v else s.gpr r) := by
  by_cases h : c <;> simp [h, setReg_self]

/-! ## What the test computes -/

/-- The bytes after the whole blocks of the first slice (of length `a`), of
a text of `len` bytes. -/
def tlsD (len a : BitVec 64) : BitVec 64 :=
  len - (a &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 32 - 16)))

/-- `r8` after the tests of the nonce's length `n`, of the additional data's
length `al` and of the bytes after the first slice's whole blocks. -/
def tls2 (n al len a : BitVec 64) : BitVec 64 :=
  if (!decide ((tlsD len a).toNat < (17#64).toNat)) = true then tlsD len a
  else if (!decide (al.toNat < (17#64).toNat)) = true then al else n - 12#64

/-- `r8` after the test of the first slice's length. -/
def tls3 (long : Bool) (n al len a : BitVec 64) : BitVec 64 :=
  tls2 n al len a |||
    if (!decide (a.toNat < (256#64).toNat)) = true then tls2 n al len a
    else (len ||| BitVec.signExtend 64 (BitVec.ofNat 32 (if long then 256 else 0))) >>> 8

/-- `r8` after the test of a last block filled by the slices after the first. -/
def tls4 (long fill : Bool) (n al len a : BitVec 64) : BitVec 64 :=
  tls3 long n al len a |||
    if (!((len &&& BitVec.signExtend 64 (BitVec.ofNat 32 (if fill then 255 else 2 ^ 32 - 1))) &&&
        (len &&& BitVec.signExtend 64 (BitVec.ofNat 32 (if fill then 255 else 2 ^ 32 - 1))) == 0)) = true then
      tls3 long n al len a
    else a &&& 15#64

/-- Whether `tlsTest long fill` takes the path of a TLS record's text. -/
def tlsGo (long fill : Bool) (s : State) : Bool :=
  decide ((tls4 long fill (s.gpr .rcx) (AL s) (BitVec.ofNat 64 (L s)) (BitVec.ofNat 64 (fl s))).toNat < (1#64).toNat)

theorem Pub.eTls {s₀ s₀' : State} (pb : Pub s₀ s₀') (long fill : Bool) : tlsGo long fill s₀' = tlsGo long fill s₀ := by
  simp only [tlsGo, AL, pb.rcx, pb.r9, pb.eL, pb.eFl]

/-! ## In one run -/

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The last block of the test. -/
theorem tlsT3_ok (long fill : Bool) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s)
    (h10 : st.gpr .r10 = BitVec.ofNat 64 (fl s)) (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.block (tlsLast long fill)) st fun st' => st'.cf = some (tlsGo long fill s) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₅ := h.slot hp (d := 40) (by decide)
  have r₃ := h.slot hp (d := 24) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have hal : st.mem.readW (W s + BitVec.ofNat 64 24) 64 = AL s := h.kept.alen
  apply WP.of_runBlock
  refine ⟨_, by simp only [tlsLast, gLen, gAlen]; xrun [h11, h10, hdx, r₅, r₃, hlen, hal, execCmov, eval,
    Option.map_some, ite_setReg], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags]; rfl
  · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, d]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

theorem w_tlsT3 (long fill : Bool) {st : State} (h : G2 s st) :
    WP isa (.block (tlsLast long fill)) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (tlsGo long fill s) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, r10⟩ := h
  refine WP.mono (tlsT3_ok hp long fill B r11 r10 dx) fun s₃ ⟨cf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
  have k : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = st.gpr r := g₃
  exact ⟨⟨B.regs m₃ cs₃ rd₃ wr₃, by rw [k _ (by decide) (by decide) (by decide) (by decide), di],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), si],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), dx],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), cx]⟩,
    by rw [k _ (by decide) (by decide) (by decide) (by decide), r11], cf₃⟩

/-- A text on the path of a TLS record's has fewer than 17 bytes after its
first slice (as `copySplit` needs). -/
theorem tls_sub {long fill : Bool} (h : tlsGo long fill s = true) : L s - fl s < 2 ^ 63 := by
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  unfold tlsGo tls4 tls3 at h
  replace h := of_decide_eq_true h
  have z : ∀ x : BitVec 64, x.toNat < (1#64).toNat → x = 0#64 := fun x hx =>
    BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat] at hx ⊢; omega)
  have h0 := z _ h
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff] at h0
  have h2 := h0.1.1
  unfold tls2 at h2
  have hd : (tlsD (BitVec.ofNat 64 (L s)) (BitVec.ofNat 64 (fl s))).toNat < 17 := by
    by_contra hc
    rw [ite_eq_left (by simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]; simpa using hc)] at h2
    rw [h2] at hc; simp at hc
  have ha : (BitVec.ofNat 64 (fl s) &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ 32 - 16))).toNat ≤ fl s := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.and_le_left
  unfold tlsD at hd
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL] at hd
  omega

/-- The test of a TLS record's text. -/
theorem tlsTest_wp (long fill : Bool) {st : State} (h : E2 s st) :
    WP isa (tlsTest long fill) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (tlsGo long fill s) :=
  lenTest_wp hp (fun _ G => w_tlsT3 hp long fill G) h

end

/-! ## In two runs -/

theorem tlsT3_check (long fill : Bool) :
    ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block (tlsLast long fill).dropLast) hc).isSome = true := by
  cases long <;> cases fill <;>
    exact ⟨_, by simp only [tlsLast, gLen, gAlen, imm, List.dropLast, Bool.false_eq_true, ↓reduceIte]; taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

omit hp hp' in
/-- The last block of the test, from two states. -/
theorem tlsLast_eq2 (long fill : Bool) {υ₁ υ₂ : State} (H₁ : G2 s₀ υ₁) (H₂ : G2 s₀' υ₂) :
    RelCT isa (Eq2 υ₁ υ₂) (.block (tlsLast long fill)) TT := by
  have w₁ : υ₁.gpr .r11 = W s₀ := H₁.2.1
  have w₂ : υ₂.gpr .r11 = W s₀ := by rw [H₂.2.1, pb.w]
  refine rel_block_split (l₁ := (tlsLast long fill).dropLast) (l₂ := [.alu .cmp .r8 (imm 1)])
    (RelCT.seq (R := fun _ _ => True) ?_ (rel_cmpImm .r8 1))
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [w₁, w₂]) (tlsT3_check long fill)

/-- The test of a TLS record's text, in two runs. -/
theorem tlsTest_rel (long fill : Bool) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (tlsTest long fill) fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (tlsGo long fill s₀)) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (tlsGo long fill s₀')) :=
  pstep (rel_of_eq2 fun _ _ h => lenTest_eq2 hp hp' pb (fun _ _ H₁ H₂ => tlsLast_eq2 pb long fill H₁ H₂) h.1 h.2)
    (fun _ h => tlsTest_wp hp long fill h) (fun _ h => tlsTest_wp hp' long fill h)

end

theorem tlsTest_mx (long fill : Bool) : (tlsTest long fill : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl
theorem tlsTest_spAll (long fill : Bool) : (tlsTest long fill : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := rfl
theorem tlsTest_xdepth (long fill : Bool) : (tlsTest long fill : Prog isa).x86_64Depth = 0 := rfl

end VG.Proof.AesGcm.X86_64.Gather
