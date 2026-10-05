import VerifiedGarbage.Proof.Rsa.X86_64.RpMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode

/-!
# `vg_rsa_recover_primes` on x86-64: correctness

`Recover.code mul`, from a state its contract allows, writes `primesKey` of
its inputs (`rpCode_correct`), against `rpContract`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_recover_primes(p = rdi, p_len = rsi, q = rdx, q_len = rcx,
n = r8, n_len = r9, e = [rsp + 8], e_len = [rsp + 16], d = [rsp + 24],
d_len = [rsp + 32], scratch = [rsp + 40], scratch_len = [rsp + 48])`. -/
def rpContract : Contract isa where
  pre s :=
    let p : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let q : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let n : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let e : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let d : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
      p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
      q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint d ∧
      ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r9).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .r9).toNat ∧
      (s.gpr .rcx).toNat = (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat ≤ (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat ≤ (s.gpr .r9).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r9).toNat ≤ (stackArg s 5).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .rdi, (s.gpr .r9).toNat), (s.gpr .rdx, (s.gpr .r9).toNat)]
      ((s'.gpr .rax).setWidth 32)
      ((Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).1.map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat ∧
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat)
        (Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 2) (stackArg s₁ 3).toNat)).2 =
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat)
        (Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 2) (stackArg s₂ 3).toNat)).2

/-! ## The entry -/

theorem rpEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 40 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sP) .rdi, .store (hdr11 sQ) .rdx, .store (hdr11 Impl.Bignum.X86_64.Public.sN) .r8,
    .store (hdr11 Impl.Bignum.X86_64.Public.sK) .r9] : List Instr) ++
    (crtPairs [(0, Impl.Bignum.X86_64.Public.sE), (1, Impl.Bignum.X86_64.Public.sElen), (2, sD), (3, sDl)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def rpEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) : Mem :=
  (((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sQ)) vq).writeW (off B (8 * Impl.Bignum.X86_64.Public.sN)) vn).writeW
    (off B (8 * Impl.Bignum.X86_64.Public.sK)) vk

/-- The header after the entry's stores. -/
def rpEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) : Mem :=
  ((((rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk).writeW (off B (8 * Impl.Bignum.X86_64.Public.sE)) ve).writeW
    (off B (8 * Impl.Bignum.X86_64.Public.sElen)) vel).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem rpEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) :
    Outside B 0 (8 * 32) m (rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk) := by
  unfold rpEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem rpEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) :
    let m' := rpEntryMem m B v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧
    word m' B (8 * Impl.Bignum.X86_64.Public.sN) = vn ∧ word m' B (8 * Impl.Bignum.X86_64.Public.sK) = vk ∧
    word m' B (8 * Impl.Bignum.X86_64.Public.sE) = ve ∧ word m' B (8 * Impl.Bignum.X86_64.Public.sElen) = vel ∧
    word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' rpEntryMem rpEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 4) in `rdi`. -/
theorem rpEntry_ok {s : State} {B : Addr} (hB : stackArg s 4 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 5, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem B (8 * sP) = s.gpr .rdi ∧ word t.mem B (8 * sQ) = s.gpr .rdx ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sN) = s.gpr .r8 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sK) = s.gpr .r9 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sE) = stackArg s 0 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = stackArg s 1 ∧
      word t.mem B (8 * sD) = stackArg s 2 ∧ word t.mem B (8 * sDl) = stackArg s 3 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
  have hB' : s.mem.readW (stackArgAddr s 4) 64 = B := hB
  have ha4 := ha 4 (by decide)
  rw [rpEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = rpEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e4, ha4, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sP (by decide),
      hw sQ (by decide), hw Impl.Bignum.X86_64.Public.sN (by decide), hw Impl.Bignum.X86_64.Public.sK (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact rpEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = rpEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho⟩ :=
    rpEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3)
  refine ⟨hdi, fun i hi => ?_, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Rsa.X86_64
