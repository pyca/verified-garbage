import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# RSA with the CRT on x86-64: the entry

`Crt.entry` saves the callee-saved registers and the arguments (the pointers
and lengths among them `main` reads, some from the stack) in the header of
the working space, and leaves its base in `rdi` (`crtEntry_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Stack argument `j` (from 0) into `rax`, then into header slot `i` at `r11`. -/
def crtPair (j i : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := 8 * ((j + 1 : Nat) : Int) }), .store (hdr11 i) .rax]

/-- `crtPair` for each `(j, i)`. -/
def crtPairs : List (Nat × Nat) → List Instr
  | [] => []
  | p :: ps => crtPair p.1 p.2 ++ crtPairs ps

theorem crtEntry_eq : Crt.entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rcx, .store (hdr11 sIn) .r8] : List Instr) ++
    (crtPairs [(0, sP), (1, sPlen), (2, sQ), (3, sQlen), (4, sDp), (6, sDq), (8, sQinv)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

theorem stackArgAddr_disp (s : State) (j : Nat) :
    s.gpr .rsp + BitVec.ofInt 64 (8 * ((j + 1 : Nat) : Int)) = stackArgAddr s j := by
  rw [show (8 * ((j + 1 : Nat) : Int)) = ((8 * (j + 1) : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rfl

/-- One stack argument into the header. -/
theorem crtPair_ok {t : State} {B A : Addr} {j i : Nat} {v : BitVec 64} (h11 : t.gpr .r11 = B)
    (hA : t.gpr .rsp + BitVec.ofInt 64 (8 * ((j + 1 : Nat) : Int)) = A)
    (ha : InRegions (t.rd ++ t.wr) A 8) (hv : t.mem.readW A 64 = v) (hw : InRegions t.wr (off B (8 * i)) 8) :
    WP isa (.block (crtPair j i)) t fun t' => t'.mem = t.mem.writeW (off B (8 * i)) v ∧ Keep [.rax] t t' :=
  WP.keep [.rax] (by xrun [crtPair, State.ea, hdr11, hA, ha, hv, h11, hdrOff, hw]) rfl

/-- The stack arguments `p.1` into the header slots `p.2`, for `p ∈ ps`. -/
theorem crtPairs_ok {s : State} {B : Addr} : ∀ (ps : List (Nat × Nat)) (t : State),
    (∀ p ∈ ps, p.2 < 32 ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s p.1) 8 ∧
      (∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s p.1) 64 = stackArg s p.1) ∧
      InRegions s.wr (off B (8 * p.2)) 8) →
    t.gpr .r11 = B → t.gpr .rsp = s.gpr .rsp → t.rd = s.rd → t.wr = s.wr → Outside B 0 (8 * 32) s.mem t.mem →
    WP isa (.block (crtPairs ps)) t fun t' =>
      t'.mem = ps.foldl (fun m p => m.writeW (off B (8 * p.2)) (stackArg s p.1)) t.mem ∧ Keep [.rax] t t'
  | [], _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | p :: ps, t, hps, h11, hsp, hrd, hwr, ho => by
    obtain ⟨hi, ha, hsep, hw⟩ := hps p List.mem_cons_self
    rw [show crtPairs (p :: ps) = crtPair p.1 p.2 ++ crtPairs ps from rfl, WP.block_append_iff]
    refine WP.mono (crtPair_ok h11 (by rw [hsp]; exact stackArgAddr_disp s p.1) (by rw [hrd, hwr]; exact ha)
      (hsep _ ho) (by rw [hwr]; exact hw)) fun t₁ ⟨hm, k⟩ => ?_
    refine WP.mono (crtPairs_ok ps t₁ (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (by rw [k.gpr (by decide)]; exact h11) (by rw [k.gpr (by decide)]; exact hsp) (k.2.1.trans hrd)
      (k.2.2.trans hwr) (by rw [hm]; exact Outside.store_hdr ho (by omega) (by decide) _))
      fun t' ⟨hm', k'⟩ => ⟨by rw [hm', hm]; rfl, (k.trans k').mono (by decide)⟩

/-- The header after the stores from registers. -/
def crtEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi : BitVec 64) : Mem :=
  (((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sOut)) vo).writeW
    (off B (8 * sN)) vn).writeW (off B (8 * sK)) vk).writeW (off B (8 * sIn)) vi

/-- The header after the entry's stores. -/
def crtEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((((((crtEntryMemA m B v0 v1 v2 v3 v4 v5 vo vn vk vi).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sPlen)) vpl).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sQlen)) vql).writeW
    (off B (8 * sDp)) vdp).writeW (off B (8 * sDq)) vdq).writeW (off B (8 * sQinv)) vqi

theorem crtEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi : BitVec 64) :
    Outside B 0 (8 * 32) m (crtEntryMemA m B v0 v1 v2 v3 v4 v5 vo vn vk vi) := by
  unfold crtEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem crtEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := crtEntryMem m B v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sOut) = vo ∧ word m' B (8 * sN) = vn ∧
    word m' B (8 * sK) = vk ∧ word m' B (8 * sIn) = vi ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vdp ∧
    word m' B (8 * sDq) = vdq ∧ word m' B (8 * sQinv) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' crtEntryMem crtEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `Crt.entry`: the header, from the arguments, and the working space's
base (stack argument 10) in `rdi`. -/
theorem crtEntry_ok {s : State} {B : Addr} (hB : stackArg s 10 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 11, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block Crt.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rcx ∧ word t.mem B (8 * sIn) = s.gpr .r8 ∧
      word t.mem B (8 * sP) = stackArg s 0 ∧ word t.mem B (8 * sPlen) = stackArg s 1 ∧
      word t.mem B (8 * sQ) = stackArg s 2 ∧ word t.mem B (8 * sQlen) = stackArg s 3 ∧
      word t.mem B (8 * sDp) = stackArg s 4 ∧ word t.mem B (8 * sDq) = stackArg s 6 ∧
      word t.mem B (8 * sQinv) = stackArg s 8 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = B := hB
  have ha10 := ha 10 (by decide)
  rw [crtEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = crtEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e10, ha10, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sIn (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact crtEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = crtEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho⟩ :=
    crtEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8)
  refine ⟨hdi, fun i hi => ?_, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Bignum.X86_64
