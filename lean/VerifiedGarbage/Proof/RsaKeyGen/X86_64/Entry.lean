import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry

/-!
# A candidate on x86-64: the entry

`kEntry` saves the callee-saved registers and the arguments in the header of
the scratch space, and leaves its base in `rdi` (`kEntry_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem kEntry_eq : kEntry = ([.mov .r11 (.mem { base := .rsp, disp := 32 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 kOut) .rdi, .store (hdr11 kLen) .rsi, .store (hdr11 kUsedP) .rdx, .store (hdr11 kE) .rcx,
    .store (hdr11 kElen) .r8, .store (hdr11 kP) .r9] : List Instr) ++
    ([.mov .rax (.mem { base := .rsp, disp := 8 }), .store (hdr11 kPlen) .rax] : List Instr) ++
    ([.mov .rax (.mem { base := .rsp, disp := 16 }), .store (hdr11 kRand) .rax] : List Instr) ++
    ([.mov .rax (.mem { base := .rsp, disp := 24 }), .store (hdr11 kRandLen) .rax, .mov .rdi (.reg .r11)] :
      List Instr) := rfl

/-- The header after `kEntry`'s first stores. -/
def kEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vl vu ve vel vp : BitVec 64) : Mem :=
  (((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * kOut)) vo).writeW
    (off B (8 * kLen)) vl).writeW (off B (8 * kUsedP)) vu).writeW (off B (8 * kE)) ve).writeW (off B (8 * kElen))
    vel).writeW (off B (8 * kP)) vp

theorem kEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vl vu ve vel vp : BitVec 64) :
    let m' := kEntryMem m B v0 v1 v2 v3 v4 v5 vo vl vu ve vel vp
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * kOut) = vo ∧ word m' B (8 * kLen) = vl ∧
    word m' B (8 * kUsedP) = vu ∧ word m' B (8 * kE) = ve ∧ word m' B (8 * kElen) = vel ∧
    word m' B (8 * kP) = vp ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' kEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `kEntry` leaves. -/
structure EntryPost (s t : State) (B : Addr) : Prop where
  rdi : t.gpr .rdi = B
  saved : ∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)
  out : word t.mem B (8 * kOut) = s.gpr .rdi
  len : word t.mem B (8 * kLen) = s.gpr .rsi
  usedP : word t.mem B (8 * kUsedP) = s.gpr .rdx
  e : word t.mem B (8 * kE) = s.gpr .rcx
  elen : word t.mem B (8 * kElen) = s.gpr .r8
  p : word t.mem B (8 * kP) = s.gpr .r9
  plen : word t.mem B (8 * kPlen) = stackArg s 0
  rand : word t.mem B (8 * kRand) = stackArg s 1
  rlen : word t.mem B (8 * kRandLen) = stackArg s 2
  frame : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi] s t

theorem stackArg_readW (s : State) (i : Nat) : s.mem.readW (stackArgAddr s i) 64 = stackArg s i := rfl

/-- `kEntry`: the header from the arguments, and the scratch space's base
(the fourth stack argument) in `rdi`. -/
theorem kEntry_ok {s : State} {B : Addr} (hB : stackArg s 3 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8)
    (hsep : ∀ m', Outside B 0 (8 * 32) s.mem m' → ∀ i < 3, m'.readW (stackArgAddr s i) 64 = stackArg s i) :
    WP isa (.block kEntry) s (EntryPost s · B) := by
  have hB' : s.mem.readW (stackArgAddr s 3) 64 = B := hB
  rw [kEntry_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * kOut) = s.gpr .rdi ∧ word t.mem B (8 * kLen) = s.gpr .rsi ∧
      word t.mem B (8 * kUsedP) = s.gpr .rdx ∧ word t.mem B (8 * kE) = s.gpr .rcx ∧
      word t.mem B (8 * kElen) = s.gpr .r8 ∧ word t.mem B (8 * kP) = s.gpr .r9 ∧
      Outside B 0 (8 * 32) s.mem t.mem) ?_ rfl)
    fun t₁ ⟨⟨h11, h0, h1, h2, h3, h4, h5, hO, hL, hU, hE, hEl, hP, ho₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, show s.gpr .rsp + BitVec.ofInt 64 32 = stackArgAddr s 3 from rfl, ha 3 (by decide), hB',
      hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
      hw 5 (by decide), hw kOut (by decide), hw kLen (by decide), hw kUsedP (by decide), hw kE (by decide),
      hw kElen (by decide), hw kP (by decide)]
    exact kEntryMem_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have ha₁ : ∀ i < 4, InRegions (t₁.rd ++ t₁.wr) (stackArgAddr s i) 8 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact ha i hi
  have hw₁ : ∀ i < 32, InRegions t₁.wr (off B (8 * i)) 8 := fun i hi => by rw [k₁.2.2]; exact hw i hi
  have hsp₁ : t₁.gpr .rsp = s.gpr .rsp := k₁.gpr (by decide)
  -- `p_len`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = t₁.mem.writeW (off B (8 * kPlen)) (stackArg s 0)) (by
    xrun [State.ea, hdr11, hsp₁, show s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 from rfl, ha₁ 0 (by decide),
      hsep _ ho₁ 0 (by decide), h11, hdrOff, hw₁ kPlen (by decide)]) rfl) fun t₂ ⟨⟨h11₂, hm₂⟩, k₂⟩ => ?_
  have ho₂ : Outside B 0 (8 * 32) s.mem t₂.mem := by rw [hm₂]; exact Outside.store_hdr ho₁ (by decide) (by decide) _
  have ha₂ : ∀ i < 4, InRegions (t₂.rd ++ t₂.wr) (stackArgAddr s i) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2]; exact ha₁ i hi
  have hw₂ : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi => by rw [k₂.2.2]; exact hw₁ i hi
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := (k₂.gpr (by decide)).trans hsp₁
  -- `rand`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = t₂.mem.writeW (off B (8 * kRand)) (stackArg s 1)) (by
    xrun [State.ea, hdr11, hsp₂, show s.gpr .rsp + BitVec.ofInt 64 16 = stackArgAddr s 1 from rfl, ha₂ 1 (by decide),
      hsep _ ho₂ 1 (by decide), h11₂, hdrOff, hw₂ kRand (by decide)]) rfl) fun t₃ ⟨⟨h11₃, hm₃⟩, k₃⟩ => ?_
  have ho₃ : Outside B 0 (8 * 32) s.mem t₃.mem := by rw [hm₃]; exact Outside.store_hdr ho₂ (by decide) (by decide) _
  have ha₃ : ∀ i < 4, InRegions (t₃.rd ++ t₃.wr) (stackArgAddr s i) 8 := fun i hi => by
    rw [k₃.2.1, k₃.2.2]; exact ha₂ i hi
  have hw₃ : ∀ i < 32, InRegions t₃.wr (off B (8 * i)) 8 := fun i hi => by rw [k₃.2.2]; exact hw₂ i hi
  have hsp₃ : t₃.gpr .rsp = s.gpr .rsp := (k₃.gpr (by decide)).trans hsp₂
  -- `rand_len`, and the base into `rdi`.
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = t₃.mem.writeW (off B (8 * kRandLen)) (stackArg s 2)) (by
    xrun [State.ea, hdr11, hsp₃, show s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 from rfl, ha₃ 2 (by decide),
      hsep _ ho₃ 2 (by decide), h11₃, hdrOff, hw₃ kRandLen (by decide)]) rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hs : ∀ {i j : Nat} {x : BitVec 64}, word t₁.mem B (8 * j) = x → i ≠ j → i < 32 → j < 32 →
      j ≠ kPlen → j ≠ kRand → j ≠ kRandLen → word t.mem B (8 * j) = x := fun {i j x} h _ _ hj h1 h2 h3 => by
    rw [hm, hm₃, hm₂]
    exact word_skip (word_skip (word_skip h (Ne.symm h1) (by decide) hj) (Ne.symm h2) (by decide) hj)
      (Ne.symm h3) (by decide) hj
  refine ⟨hdi, fun i hi => ?_, hs (i := 0) hO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs (i := 0) hL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs (i := 0) hU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs (i := 0) hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs (i := 0) hEl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs (i := 0) hP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_,
    (((k₁.trans k₂).trans k₃).trans k).mono (by decide)⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs (i := 9) h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hs (i := 9) h1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hs (i := 9) h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hs (i := 9) h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hs (i := 9) h4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hs (i := 9) h5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [hm, hm₃]
    exact word_skip (word_skip (by rw [hm₂]; exact word_writeW_self _ _ _ _) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide)
  · rw [hm, hm₃]; exact word_skip (word_writeW_self _ _ _ _) (by decide) (by decide) (by decide)
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact Outside.store_hdr ho₃ (by decide) (by decide) _

end VG.Proof.RsaKeyGen.X86_64
