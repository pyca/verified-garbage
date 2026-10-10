import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.DecideAt

/-! ## From `Top.lean` -/

section

/-!
# ML-DSA on AArch64: entry and exit

What the top-level functions keep from their entry state `σ` on (`Top`): the
permissions and the stack pointer, their four arguments in `x25`–`x28`, the
callee-saved registers they never write, and their caller's `x24`–`x28` and
`x30` saved in `scratch`. The prologue establishes it (`pro_ok`), every piece
keeps it (`Top.step`), and the epilogue restores the caller's registers from
it (`epi_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm wp_ldrx in_rd_wr)
open VG.Spec.Sha3 (bytesAt)

/-- The callee-saved registers the functions never write. -/
abbrev untouched : List Reg := [.x19, .x20, .x21, .x22, .x23]

/-- What the functions keep from their entry state `σ` on. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x25 : s.gpr .x25 = σ.gpr .x0
  x26 : s.gpr .x26 = σ.gpr .x1
  x27 : s.gpr .x27 = σ.gpr .x2
  x28 : s.gpr .x28 = σ.gpr .x3
  cs : ∀ r ∈ untouched, s.gpr r = σ.gpr r
  saved : ∀ k < 6, s.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0)
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

theorem untouched_kept : ∀ r ∈ untouched, r ∈ keptRegs := by decide

/-- The saved registers, in `scratch`. -/
abbrev svP : Ptr := sc SV

/-- `Top` is kept by a piece that keeps the saved registers. -/
theorem Top.step {S : Nat} {rbs wbs : List (Reg × Nat)} {σ s s' : State} (h : Top σ s) (L : Lay S rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws svP 48 = true) : Top σ s' := by
  have hsv : ∀ k < 6, s'.mem.readW (pa s' svP + BitVec.ofNat 64 (8 * k)) 64 =
      s.mem.readW (pa s svP + BitVec.ofNat 64 (8 * k)) 64 := fun k hk => by
    rw [hP.pa (L.keepBs hc)]
    obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
    refine hP.frame.readW (r := ⟨pa s svP, 48⟩) (Offset.contains_base _ (by omega) (by omega))
      (L.fdisj hc) (by decide)
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp, by rw [hP.bs _ (by decide), h.x25],
    by rw [hP.bs _ (by decide), h.x26], by rw [hP.bs _ (by decide), h.x27], by rw [hP.bs _ (by decide), h.x28],
    fun r hr => by rw [hP.cs r (untouched_kept r hr), h.cs r hr], fun k hk => ?_,
    fun r hr => (hP.vcs r hr).trans (h.vcs r hr)⟩
  have e : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e' : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s' svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, hP.bs _ (by decide), h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e', hsv k hk, ← e, h.saved k hk]

/-! ## The prologue -/

theorem pro_eq : pro = (List.range 6).map (fun k => .str .x (savedRegs.getD k .x0) .x3 (SV + 8 * k)) ++
    ([.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0, .addImm .x .x28 .x3 0,
      .movz .x .x24 1 0] : List Instr) := rfl

theorem pro_ok {σ : State} (hin : ∀ k < 6, InRegions σ.wr (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8) :
    WP isa (.block pro) σ fun s => Top σ s ∧ s.gpr .x24 = 1 ∧
      Frame [⟨σ.gpr .x3 + BitVec.ofNat 64 SV, 48⟩] σ.mem s.mem := by
  rw [pro_eq, WP.block_append_iff]
  refine WP.mono (WP.preservedV (Proof.MlKem.AArch64.KeyGen.saves_ok
    (σ.gpr .x3) .x3 SV savedRegs (by decide) (by decide) 6
    (by decide) rfl hin) (by lit_decide)) fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ e₂ => wp_addImm (by decide) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_addImm (by decide) fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have o : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  refine ⟨⟨by rw [o.rd, r₁], by rw [o.wr, w₁], by rw [o.sp, p₁], ?_, ?_, ?_, ?_, fun r hr => ?_, fun k hk => ?_,
    fun r hr => (o.vcs r hr).trans (hv₁ r hr)⟩,
    by rw [e₆]; rfl, by rw [o.mem]; exact f₁⟩
  · rw [h₆.get .x25, h₅.get .x25, h₄.get .x25, h₃.get .x25, e₂, BitVec.add_zero, g₁]
  · rw [h₆.get .x26, h₅.get .x26, h₄.get .x26, e₃, BitVec.add_zero, h₂.get .x1, g₁]
  · rw [h₆.get .x27, h₅.get .x27, e₄, BitVec.add_zero, h₃.get .x2, h₂.get .x2, g₁]
  · rw [h₆.get .x28, e₅, BitVec.add_zero, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]
  · rw [o.get r (by revert r; decide), g₁]
  · rw [o.mem]; exact z₁ k hk

/-! ## The epilogue -/

theorem epi_ok {σ s : State} (h : Top σ s) (hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.gpr .x0 = s.gpr .x24 ∧ s'.mem = s.mem := by
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 ∧
      w.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by
        rw [hr, hw, show σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 SV +
          BitVec.ofNat 64 (8 * k) by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
        exact inRegions_sub hin (by omega) (by decide), by rw [hm]; exact h.saved k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w'.rd = s.rd ∧ w'.wr = s.wr ∧ w'.mem = s.mem ∧ w'.gpr .x28 = σ.gpr .x3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_addImm (by decide) fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, h.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 5)) (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 0)) (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 1)) (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 2)) (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 3)) (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 4)) (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] s s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, h.sp], fun r hr => (o₇.vcs r hr).trans (h.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ savedRegs
    · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · have hu : r ∈ untouched := by revert r ho hr; decide
      rw [o₇.get r (by revert r hu; decide), h.cs r hu]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, BitVec.add_zero]

end VG.Proof.MlDsa.AArch64.KeyGen

end

/-! ## From `PrimsOk.lean` -/

section

/-!
# ML-DSA on AArch64: what the proofs need of the primitives

`PrimsOk P S`: each primitive of `P` is correct and constant time under its
shared contract with `S` bytes of stack, and its frames use at most those `S`
bytes (`CalleeOk`, from its `Verified` proof by `CalleeOk.of_verified`); `S`
is at least the 16 bytes the sponge functions' frames use. The proofs of
`vg_mldsa*_keygen` and `vg_mldsa*_verify` hold for any such `P`, with their
contracts' stack `S`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa

/-- Implementations of the primitives, correct and constant time with `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  s16 : 16 ≤ S
  sl : S < 2 ^ 16
  ntt : CalleeOk S P.ntt (nttContract AArch64.abi S)
  invNtt : CalleeOk S P.invNtt (nttInvContract AArch64.abi S)
  mul : CalleeOk S P.mul (mulContract AArch64.abi S)
  mulAdd : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S)
  add : CalleeOk S P.add (addContract AArch64.abi S)
  sub : CalleeOk S P.sub (subContract AArch64.abi S)
  rejNtt : CalleeOk S P.rejNtt (rejNTTContract AArch64.abi S)
  rej4 : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S)
  rejBounded : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  power2Round : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S)
  useHint : CalleeOk S P.useHint (useHintContract AArch64.abi S)
  normLt : CalleeOk S P.normLt (normLtContract AArch64.abi S)
  simpleBitPack : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  unpackT1 : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S)
  hintUnpack : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S)

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega

end VG.Proof.MlDsa.AArch64.KeyGen

end

/-! ## From `Lay.lean` -/

section

/-!
# ML-DSA key generation on AArch64: parameters and buffers

The facts about the parameter sets the proof uses (`PFacts`), the layout of
the buffers of key generation (`seed` in `x25`, read; `scratch`, `pk` and `sk`
in `x28`, `x26` and `x27`, written: `kgR`, `kgW p`), which the contract's
precondition gives from the prologue on (`kgLay`), and the checks of pointers
into them, for any parameter set, which `lay` proves from the offsets by
`omega`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by simp, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

theorem scr_eq (p : Params) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
  simp only [scrLen, scratchWords]; omega

theorem PFacts.scr {p : Params} (_ : PFacts p) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  scr_eq p

theorem PFacts.small {p : Params} (hF : PFacts p) : scrLen p < 2 ^ 32 ∧ p.pkLen < 2 ^ 32 ∧ p.skLen < 2 ^ 32 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hls : lenS p * (p.ℓ + p.k) ≤ 128 * 15 := by
    rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by rw [scr_eq]; omega, by rw [hF.pk]; omega, by rw [hF.sk, oT0]; omega⟩

/-! ## The layout -/

/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.x25, 32)]
/-- `scratch`, `pk` and `sk`. -/
abbrev kgW (p : Params) : List (Reg × Nat) := [(.x28, scrLen p), (.x26, p.pkLen), (.x27, p.skLen)]

theorem le_of_wfP {S sp : Nat} (h : wfP S sp) : S ≤ sp := by
  unfold wfP at h; split at h <;> omega

/-- The stack below the stack pointer is apart from the regions, from the
contract's evaluated precondition. -/
theorem below_of_resv {S : Nat} {sp : Addr} {a b c d : Region}
    (h : Sig.conj ((stackBelow sp S).map fun r => [r.Disjoint a, r.Disjoint b, r.Disjoint c, r.Disjoint d]).flatten) :
    (below sp S).Disjoint a ∧ (below sp S).Disjoint b ∧ (below sp S).Disjoint c ∧ (below sp S).Disjoint d := by
  rcases S with _ | S
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> exact fun x h _ => by simp [Region.Contains] at h
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Sig.conj_cons] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem inR_self {X : List Region} {r : Region} (h : r ∈ X) : InRegions X r.base r.len :=
  ⟨r, h, Region.contains_self _ _⟩

/-- Additional immutable read-only regions are allowed internally; the original
writable-buffer, aliasing and stack requirements remain unchanged. -/
def kgPre (p : Params) (S : Nat) (σ : State) : Prop :=
  (Spec.MlDsa.keyGenContract p AArch64.abi S).pre
    {σ with rd := [⟨σ.gpr .x0, 32⟩]} ∧ ⟨σ.gpr .x0, 32⟩ ∈ σ.rd

theorem kgPre_of_shared {p : Params} {S : Nat} {σ : State}
    (h : (Spec.MlDsa.keyGenContract p AArch64.abi S).pre σ) : kgPre p S σ := by
  have hr : σ.rd = [⟨σ.gpr .x0, 32⟩] := by
    sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
    exact h.2.1
  refine ⟨?_, by rw [hr]; simp⟩
  have he : ({σ with rd := [⟨σ.gpr .x0, 32⟩]} : State) = σ := by rw [← hr]
  simpa only [he] using h

theorem kgLay {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) (h : Top σ s) : Lay S kgR (kgW p) s := by
  obtain ⟨hp, hseed⟩ := hp
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp
  obtain ⟨hwf, hwr, d01, d02, d03, d12, d13, d23, hres, n0, n1, n2, n3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := below_of_resv hres
  have hS : S ≤ σ.sp.toNat := le_of_wfP hwf
  have hsm := hF.small
  have e25 := h.x25; have e26 := h.x26; have e27 := h.x27; have e28 := h.x28
  have mrd : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr => by
    rw [h.rd, h.wr]; exact inR_self hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [h.sp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl)
    exacts [by decide, hsm.1, hsm.2.1, hsm.2.2]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) b' (rfl | rfl | rfl | rfl) hne hw <;>
      first
        | exact absurd rfl hne
        | simp only [e25, e26, e27, e28]
          first
            | with_reducible assumption
            | exact Region.Disjoint.symm (by assumption)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28, h.sp] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    · exact mrd ⟨σ.gpr .x0, 32⟩ (List.mem_append_left _ hseed)
    · exact mrd ⟨σ.gpr .x3, scrLen p⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x1, p.pkLen⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x2, p.skLen⟩ (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e26, e27, e28, h.wr]
    · exact inR_self (r := ⟨σ.gpr .x3, scrLen p⟩) (by rw [hwr]; simp)
    · exact inR_self (r := ⟨σ.gpr .x1, p.pkLen⟩) (by rw [hwr]; simp)
    · exact inR_self (r := ⟨σ.gpr .x2, p.skLen⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp

theorem kgOk (p : Params) : LayOk (kgR ++ kgW p) := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp

/-! ## Checks of pointers, by `omega` -/

theorem inB_x25 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x25, o) l = decide (o + l ≤ 32) := rfl
theorem inB_x28 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_x26 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl
theorem inB_x28W (p : Params) (o l : Nat) : inB (kgW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_x26W (p : Params) (o l : Nat) : inB (kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27W (p : Params) (o l : Nat) : inB (kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl

theorem sepB_kg {p : Params} {r r' : Reg} (h : r ≠ r') (hr : r ∈ [Reg.x25, .x26, .x27, .x28])
    (hr' : r' ∈ [Reg.x25, .x26, .x27, .x28]) (o l o' l' : Nat) :
    sepB kgR (kgW p) (r, o) l (r', o') l' = (inB (kgR ++ kgW p) (r, o) l && inB (kgR ++ kgW p) (r', o') l') := by
  refine sepB_ne h ?_ o l o' l'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;> first | exact absurd rfl h | rfl

/-- Unfolds the checks of pointers into the layout into arithmetic, then
`omega` (in each case of `η`). -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlDsa.AArch64.keepB,
        VG.Proof.MlDsa.AArch64.sepB_same, VG.Proof.MlDsa.AArch64.KeyGen.sepB_kg,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x25, VG.Proof.MlDsa.AArch64.KeyGen.inB_x26,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x27, VG.Proof.MlDsa.AArch64.KeyGen.inB_x28,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x26W, VG.Proof.MlDsa.AArch64.KeyGen.inB_x27W,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x28W, List.all_cons, List.all_nil, List.cons_append, List.nil_append,
        List.all_append, Bool.and_self,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true,
        ↓reduceIte, Bool.false_eq_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oR4, VG.Impl.MlDsa.AArch64.KeyGen.oSA4, VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.oSA,
        VG.Impl.MlDsa.AArch64.KeyGen.oSB, VG.Impl.MlDsa.AArch64.KeyGen.oHX, VG.Impl.MlDsa.AArch64.KeyGen.oKL,
        VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.KeyGen.SV, VG.Impl.MlDsa.AArch64.KeyGen.oT0, $ls,*]
      and_intros <;> omega_arith))

/-- A check about the layout that mentions no variable but the parameter set and
bounded indices, decided for each parameter set (`decide_at`): cheaper than
`lay`, which unfolds it into arithmetic on the parameters for `omega`, unless
there are many indices to try. -/
syntax "layd" : tactic
macro_rules
  | `(tactic| layd) => `(tactic| (
      have hmem := (‹VG.Proof.MlDsa.AArch64.KeyGen.PFacts _›).mem; decide_at hmem))

end VG.Proof.MlDsa.AArch64.KeyGen

end
