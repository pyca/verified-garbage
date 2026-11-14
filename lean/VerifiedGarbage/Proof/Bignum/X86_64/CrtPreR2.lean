module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Impl.Rsa.X86_64.Crt
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy

/-!
# RSA with the CRT on x86-64: `R² mod n` from the key's precomputed values

`vg_rsa_private_crt_precomputed` copies `R² mod n` from the key's
precomputed values `pre`, its stack argument 12, rather than computing it
(`r2Pre`): `r2Pre_ok` gives what `R2w.choice_ok` gives of the computation,
from a state where `pre`'s address and its words `w` to `2 w - 1` are
outside the working space (`PreR2`), which every step that changes only the
working space and keeps the stack pointer keeps (`PreR2.congr`). It leaks
only the stack pointer, `w`, the working space and `pre`'s address
(`r2Pre_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Stack argument 12, `pre`, and its `n` words from `k`, whose value is `V`,
outside the working space at `B` of `Z` bytes. -/
structure PreW (t : State) (B : Addr) (Z k n V : Nat) : Prop where
  arg : InRegions (t.rd ++ t.wr) (stackArgAddr t 12) 8
  argOut : ∀ b < 8, Z ≤ ofs B (stackArgAddr t 12 + BitVec.ofNat 64 b)
  rd : ∀ j < n, InRegions (t.rd ++ t.wr) (off (stackArg t 12) (8 * k + 8 * j)) 8
  out : ∀ j < n, ∀ b < 8, Z ≤ ofs B (off (stackArg t 12) (8 * k + 8 * j) + BitVec.ofNat 64 b)
  val : wv t.mem (stackArg t 12) (8 * k) n = V

/-- `pre`'s address, after a step that changes only the working space and
keeps the stack pointer. -/
theorem PreW.arg_eq {t t' : State} {B : Addr} {Z k n V : Nat} (h : PreW t B Z k n V)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) : stackArg t' 12 = stackArg t 12 := by
  have ha : stackArgAddr t' 12 = stackArgAddr t 12 := by unfold stackArgAddr; rw [hsp]
  unfold stackArg
  rw [ha]
  exact Mem.readW_congr fun b hb => hi _ (h.argOut b hb)

/-- `PreW` holds after a step that changes only the working space and
keeps the stack pointer and the regions. -/
theorem PreW.congr {t t' : State} {B : Addr} {Z k n V : Nat} (h : PreW t B Z k n V)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    PreW t' B Z k n V := by
  have ha : stackArgAddr t' 12 = stackArgAddr t 12 := by unfold stackArgAddr; rw [hsp]
  have hv := h.arg_eq hi hsp
  refine ⟨by rw [ha, hrd, hwr]; exact h.arg, fun b hb => by rw [ha]; exact h.argOut b hb,
    fun j hj => by rw [hv, hrd, hwr]; exact h.rd j hj, fun j hj => by rw [hv]; exact h.out j hj, ?_⟩
  rw [hv, ← h.val]
  exact wv_congr fun j hj => Mem.readW_congr fun b hb => hi _ (h.out j hj b hb)

/-- `pre`'s words `w` to `2 w - 1`, `R² mod N`. -/
abbrev PreR2 (t : State) (B : Addr) (Z w N : Nat) : Prop := PreW t B Z w w (2 ^ (128 * w) % N)

theorem PreR2.arg_eq {t t' : State} {B : Addr} {Z w N : Nat} (h : PreR2 t B Z w N)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) : stackArg t' 12 = stackArg t 12 :=
  PreW.arg_eq h hi hsp

theorem PreR2.congr {t t' : State} {B : Addr} {Z w N : Nat} (h : PreR2 t B Z w N)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    PreR2 t' B Z w N :=
  PreW.congr h hi hsp hrd hwr

/-- `r2Pre`'s block. -/
abbrev r2PreBlk : List Instr :=
  ([.mov .rsi (.mem preArg)] : List Instr) ++ eightW ++
    ([.alu .add .rsi (.reg .rax), .mov .rbx (.mem (hdr (sArr aR2)))] : List Instr)

theorem r2Pre_eq : r2Pre = .seq (.block r2PreBlk) copyWords := rfl

/-- `r2Pre`'s block: `pre`'s word `w` into `rsi` and `aR2` into `rbx`. -/
theorem r2PreBlk_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hp : PreR2 s B Z w N) :
    WP isa (.block r2PreBlk) s fun t => t.gpr .rsi = off (stackArg s 12) (8 * w) ∧
      t.gpr .rbx = off B (slot w aR2) ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rbx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have e104 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
  have hA : s.mem.readW (stackArgAddr s 12) 64 = stackArg s 12 := rfl
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 w → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * w) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_arith
  have hoff : stackArg s 12 + BitVec.ofNat 64 (8 * w) = off (stackArg s 12) (8 * w) := rfl
  refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off (stackArg s 12) (8 * w) ∧
      t.gpr .rbx = off B (slot w aR2) ∧ t.mem = s.mem) (by
    unfold r2PreBlk eightW preArg stk
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl (sArr aR2) (by decide), hg.hdr.harr aR2 (by decide),
      h12, hax8 _ rfl, hoff]) rfl) fun t ⟨⟨hsi, hbx, hm⟩, k⟩ => ⟨hsi, hbx, hm, k⟩

/-- `r2Pre`: `R² mod N` from `pre` into `aR2`, as `R2w.choice_ok`
computes it. -/
theorem r2Pre_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hN : 0 < N) (hp : PreR2 s B Z w N) :
    WP isa r2Pre s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hsR := slot_le (w := w) (show aR2 < 8 by decide)
  rw [r2Pre_eq]
  refine WP.seq (WP.mono (r2PreBlk_ok hg hZ h12 hp) fun t₁ ⟨hsi, hbx, hm₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h12₁ : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  refine WP.mono (copyWords_ok hsi hbx h12₁ (by omega_arith) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hp.rd j hj) (fun j hj => hs₁.st (by omega_arith))
    (fun j hj b hb => Or.inr (by have := hp.out j hj b hb; omega_arith)))
    fun t ⟨hv, _, ho, k⟩ => ?_
  rw [hm₁] at hv ho
  have k₂ := k₁.trans k
  have hvR : wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % N := by rw [hv, hp.val]
  have hA₂ : Arrays B w [aR2] s.mem t.mem :=
    Arrays.of_outside (w := w) (j := aR2) (by simp) ho (Nat.le_refl _) (by omega_arith)
  have hpow : 2 ^ (128 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  refine ⟨⟨hg.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg.rdi, ?_⟩, by rw [hvR]; exact Nat.mod_lt _ hN,
    by rw [hvR, Nat.mod_mod, hpow], ?_, k₂.mono (by decide)⟩
  · exact hA₂.hdr hg.hdr
  · exact Frm.of_arrays hA₂ (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp [r2Ranges])

/-! ## Constant time -/

/-- The public data of `r2Pre`: the stack pointer, the working space, `w`
and `pre`'s address. -/
structure R2PPub where
  sp : Addr
  B : Addr
  w : Nat
  A : Addr

/-- Before `r2Pre`. -/
def R2PreCT (p : R2PPub) (s : State) : Prop :=
  s.gpr .rsp = p.sp ∧ s.gpr .rdi = p.B ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧
    WP isa (.block r2PreBlk) s fun t => t.gpr .rsi = off p.A (8 * p.w) ∧ t.gpr .rbx = off p.B (slot p.w aR2) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w

/-- `r2Pre` leaks the same in runs that agree on its public data. -/
theorem r2Pre_ct : RelCT isa (Two R2PreCT) r2Pre fun _ _ => True := by
  rw [r2Pre_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : R2PPub) t => t.gpr .rsi = off p.A (8 * p.w) ∧
      t.gpr .rbx = off p.B (slot p.w aR2) ∧ t.gpr .r12 = BitVec.ofNat 64 p.w) [.rsp, .rdi, .r12]
    (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) fun _ _ h => h.2.2.2) ?_
  exact two_taint [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide)

/-- `R2PreCT` from `r2Pre_ok`'s hypotheses. -/
theorem r2PreCT_of {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hp : PreR2 s B Z w N) :
    R2PreCT ⟨s.gpr .rsp, B, w, stackArg s 12⟩ s :=
  ⟨rfl, hg.rdi, h12, WP.mono (r2PreBlk_ok hg hZ h12 hp) fun t ⟨hsi, hbx, _, k⟩ =>
    ⟨hsi, hbx, (k.gpr (by decide)).trans h12⟩⟩

end VG.Proof.Bignum.X86_64
