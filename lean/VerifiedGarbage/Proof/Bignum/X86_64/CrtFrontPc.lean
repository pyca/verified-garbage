module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtLoadPre
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: `n`'s setup

`pre`, the stack argument 12, and its `W` words (`PreSrc`), outside the
working space; and `n`'s setup taking `R² mod n` from it (`nPartPc_ok`),
right if `pre` holds it.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The stack argument 12 is `P`, and `P`'s `W` words are readable; both are
outside the working space at `B` of `Z` bytes. -/
structure PreSrc (s : State) (B : Addr) (Z : Nat) (P : Addr) (W : Nat) : Prop where
  arg : InRegions (s.rd ++ s.wr) (stackArgAddr s 12) 8
  argOut : ∀ b < 8, Z ≤ ofs B (stackArgAddr s 12 + BitVec.ofNat 64 b)
  val : s.mem.readW (stackArgAddr s 12) 64 = P
  rd : ∀ i < W, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8
  out : ∀ i < W, ∀ b < 8, Z ≤ ofs B (off P (8 * i) + BitVec.ofNat 64 b)

theorem PreSrc.congrK {s t : State} {B : Addr} {Z : Nat} {P : Addr} {W : Nat} {rs : List Reg}
    (h : PreSrc s B Z P W) (hm : InScr B Z s.mem t.mem) (k : Keep rs s t) (hsp : Reg.rsp ∉ rs) :
    PreSrc t B Z P W := by
  have e : stackArgAddr t 12 = stackArgAddr s 12 := by unfold stackArgAddr; rw [k.1 _ hsp]
  refine ⟨by rw [e, k.2.1, k.2.2]; exact h.arg, fun b hb => by rw [e]; exact h.argOut b hb, ?_,
    fun i hi => by rw [k.2.1, k.2.2]; exact h.rd i hi, h.out⟩
  rw [e, ← h.val]
  exact Mem.readW_congr fun b hb => hm _ (h.argOut b hb)

/-- `pre`'s words do not change with the working space. -/
theorem PreSrc.wv_eq {s : State} {B : Addr} {Z : Nat} {P : Addr} {W : Nat} (h : PreSrc s B Z P W)
    {m : Mem} (hm : InScr B Z s.mem m) {d n : Nat} (hdn : d + n ≤ W) : wv m P (8 * d) n = wv s.mem P (8 * d) n :=
  wv_congr fun i hi => Mem.readW_congr fun b hb => hm _ (by
    have := h.out (d + i) (by omega) b hb; rwa [show 8 * (d + i) = 8 * d + 8 * i by omega] at this)

theorem nSetup_pc (M : Mont) : nSetup M.mm true =
    (loadSteps ++ restSteps) ++ ([seqs (loadPre Public.aR2 offN)] ++ [M.mm Public.aXm Public.aX Public.aR2]) := rfl

/-- `n`'s setup, taking `R² mod n` from word `w` of `pre`: right if `pre`
holds it there. -/
theorem nPartPc_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {P : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) (hpre : PreSrc s B Z P W)
    (hW : 2 * ((k + 7) / 8) ≤ W) :
    WP isa (seqs (nSetup M.mm true)) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (wv s.mem P (8 * ((k + 7) / 8)) ((k + 7) / 8) =
          2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb) := by
  obtain ⟨hodd, hN1, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  have sR := slot_le (w := (k + 7) / 8) (show Public.aR2 < 8 by decide)
  rw [nSetup_pc]
  refine nPartWith_ok M h hv fun t₁ minv so f₁ k₁ => ?_
  have i₁ : InScr B Z s.mem t₁.mem := InScr.of_frm f₁ (hZs (setupRanges_le _))
  have hp₁ := hpre.congrK i₁ k₁ (by decide)
  have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
    so.good.scr.ld (by have := hdr_lt_slot ((k + 7) / 8) 8 hi; omega_arith)
  refine WP.mono (loadPre_ok so.good hZ (by omega_arith) (by omega_arith) (by decide) (by decide) hp₁.arg
    hp₁.val (d := (k + 7) / 8)
    (fun t kt ot => by
      have hlt : InRegions (t.rd ++ t.wr) (off B (8 * sW)) 8 := by rw [kt.2.1, kt.2.2]; exact hl sW (by decide)
      have hwt : word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
        rw [ot.word (.inl (by have := hdr_lt_slot ((k + 7) / 8) Public.aR2 (show sW < 32 by decide); omega_arith))
          (by unfold sW; omega)]
        exact so.good.hdr.hw
      exact WP.keep [.rax] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 ((k + 7) / 8) ∧ t'.mem = t.mem)
        (by xrun [offN, State.ea, hdr, (kt.gpr (by decide)).trans so.good.rdi, hdrOff, hlt, hwt]) rfl |>.mono
          fun t' ⟨⟨a, b⟩, c⟩ => ⟨a, b, c.mono (by decide)⟩)
    (fun i hi => by rw [show 8 * ((k + 7) / 8) + 8 * i = 8 * ((k + 7) / 8 + i) by omega]; exact hp₁.rd _ (by omega))
    (fun i hi b hb => .inr (by
      have := hp₁.out ((k + 7) / 8 + i) (by omega) b hb
      rw [show 8 * ((k + 7) / 8) + 8 * i = 8 * ((k + 7) / 8 + i) by omega]; omega_arith)))
    fun t₂ ⟨hv₂, ho₂, k₂⟩ => ?_
  rw [hpre.wv_eq i₁ (by omega), so.n] at hv₂
  have hH₂ : Hdr t₂.mem B ((k + 7) / 8) minv := (Arrays.of_outside (js := [Public.aR2]) (List.mem_singleton_self _)
    ho₂ (Nat.le_refl _) (Nat.le_refl _)).hdr so.good.hdr
  refine ⟨⟨so.good.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans so.good.rdi, hH₂⟩, ?_, fun hok => ?_,
    Frm.of_outside ho₂ (by simp [r2Ranges]), k₂⟩
  · rw [hv₂]; split <;> omega
  · have hlt : 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb < Spec.Rsa.os2ip nb :=
      Nat.mod_lt _ (by omega)
    rw [hv₂, hok]; simp only [hlt, ↓reduceIte, Nat.mod_mod]

end VG.Proof.Bignum.X86_64
