import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey

/-!
# `vg_rsa_check_key` on x86-64: the entry

`entry` saves the callee-saved registers and the arguments (some from the
stack) in the header of the working space, leaves its base in `rdi`, and
`e` and its length in `r8` and `r9` for `expCheck` (`keyEntry_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK)

theorem keyEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sN) .rdi, .store (hdr11 sK) .rsi, .store (hdr11 sE) .rdx, .store (hdr11 sElen) .rcx,
    .store (hdr11 sD) .r8, .store (hdr11 sDlen) .r9] : List Instr) ++
    (crtPairs [(0, sP), (1, sPlen), (2, sQ), (3, sQlen), (4, sDP), (6, sDQ), (8, sQI)] ++
      ([.mov .rdi (.reg .r11), .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def keyEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl : BitVec 64) : Mem :=
  (((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sN)) vn).writeW
    (off B (8 * sK)) vk).writeW (off B (8 * sE)) ve).writeW (off B (8 * sElen)) vel).writeW
    (off B (8 * sD)) vd).writeW (off B (8 * sDlen)) vdl

/-- The header after the entry's stores. -/
def keyEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi : BitVec 64) :
    Mem :=
  (((((((keyEntryMemA m B v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sPlen)) vpl).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sQlen)) vql).writeW
    (off B (8 * sDP)) vdp).writeW (off B (8 * sDQ)) vdq).writeW (off B (8 * sQI)) vqi

theorem keyEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl : BitVec 64) :
    Outside B 0 (8 * 32) m (keyEntryMemA m B v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl) := by
  unfold keyEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem keyEntryMem_facts (m : Mem) (B : Addr)
    (v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := keyEntryMem m B v0 v1 v2 v3 v4 v5 vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sN) = vn ∧ word m' B (8 * sK) = vk ∧
    word m' B (8 * sE) = ve ∧ word m' B (8 * sElen) = vel ∧ word m' B (8 * sD) = vd ∧
    word m' B (8 * sDlen) = vdl ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDP) = vdp ∧
    word m' B (8 * sDQ) = vdq ∧ word m' B (8 * sQI) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold m' keyEntryMem keyEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `entry` leaves. -/
structure EntryPost (s : State) (B : Addr) (t : State) : Prop where
  rdi : t.gpr .rdi = B
  r8 : t.gpr .r8 = s.gpr .rdx
  r9 : t.gpr .r9 = s.gpr .rcx
  saved : ∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)
  hN : word t.mem B (8 * sN) = s.gpr .rdi
  hK : word t.mem B (8 * sK) = s.gpr .rsi
  hD : word t.mem B (8 * sD) = s.gpr .r8
  hDl : word t.mem B (8 * sDlen) = s.gpr .r9
  hP : word t.mem B (8 * sP) = stackArg s 0
  hPl : word t.mem B (8 * sPlen) = stackArg s 1
  hQ : word t.mem B (8 * sQ) = stackArg s 2
  hQl : word t.mem B (8 * sQlen) = stackArg s 3
  hDP : word t.mem B (8 * sDP) = stackArg s 4
  hDQ : word t.mem B (8 * sDQ) = stackArg s 6
  hQI : word t.mem B (8 * sQI) = stackArg s 8
  out : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi, .r8, .r9] s t

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 10) in `rdi`. -/
theorem keyEntry_ok {s : State} {B : Addr} (hB : stackArg s 10 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 11, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s (EntryPost s B) := by
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = B := hB
  have ha10 := ha 10 (by decide)
  rw [keyEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = keyEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e10, ha10, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sN (by decide),
      hw sK (by decide), hw sE (by decide), hw sElen (by decide), hw sD (by decide), hw sDlen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact keyEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.rdi, .r8, .r9] (Q := fun t => t.gpr .rdi = B ∧ t.gpr .r8 = s.gpr .rdx ∧
      t.gpr .r9 = s.gpr .rcx ∧ t.mem = t₂.mem) (by
    xrun [h11₂, k12.gpr (r := .rdx) (by decide), k12.gpr (r := .rcx) (by decide)]) rfl)
    fun t ⟨⟨hdi, h8, h9, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = keyEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
      (stackArg s 1) (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8) := by
    rw [hm, hm₂, hm₁]; rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hN, hK, -, -, hD, hDl, hP, hPl, hQ, hQl, hDP, hDQ, hQI, ho⟩ :=
    keyEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
      (stackArg s 1) (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8)
  rw [← hmem] at h0 h1 h2 h3 h4 h5 hN hK hD hDl hP hPl hQ hQl hDP hDQ hQI ho
  refine ⟨hdi, h8, h9, fun i hi => ?_, hN, hK, hD, hDl, hP, hPl, hQ, hQl, hDP, hDQ, hQI, ho,
    (k12.trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Rsa.X86_64
