module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_precompute` on x86-64: the entry

`entry` saves the callee-saved registers and the arguments (some from the
stack) in the header of the working space, in `vg_rsa_check_key`'s slots,
`pre` and `pre_len` in `e`'s, `n` also as `d`, `p` as `dP` and `qInv` and
`q` as `dQ`, and leaves its base in `rdi` (`ppEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK)

theorem ppEntry_eq : Impl.Rsa.X86_64.PrivPre.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sN) .rdx, .store (hdr11 sK) .rcx, .store (hdr11 sE) .rdi, .store (hdr11 sElen) .rsi,
    .store (hdr11 sD) .rdx, .store (hdr11 sDlen) .rcx, .store (hdr11 sP) .r8, .store (hdr11 sPlen) .r9,
    .store (hdr11 sDP) .r8, .store (hdr11 sQI) .r8] : List Instr) ++
    (crtPairs [(0, sQ), (0, sDQ), (1, sQlen)] ++ ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def ppEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl : BitVec 64) : Mem :=
  (((((((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sN)) vn).writeW
    (off B (8 * sK)) vk).writeW (off B (8 * sE)) vo).writeW (off B (8 * sElen)) vol).writeW
    (off B (8 * sD)) vn).writeW (off B (8 * sDlen)) vk).writeW (off B (8 * sP)) vp).writeW (off B (8 * sPlen)) vpl).writeW
    (off B (8 * sDP)) vp).writeW (off B (8 * sQI)) vp

/-- The header after the entry's stores. -/
def ppEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl vq vql : BitVec 64) : Mem :=
  (((ppEntryMemA m B v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl).writeW (off B (8 * sQ)) vq).writeW
    (off B (8 * sDQ)) vq).writeW (off B (8 * sQlen)) vql

theorem ppEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (ppEntryMemA m B v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl) := by
  unfold ppEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem ppEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl vq vql : BitVec 64) :
    let m' := ppEntryMem m B v0 v1 v2 v3 v4 v5 vn vk vo vol vp vpl vq vql
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sN) = vn ∧ word m' B (8 * sK) = vk ∧
    word m' B (8 * sE) = vo ∧ word m' B (8 * sElen) = vol ∧
    word m' B (8 * sD) = vn ∧ word m' B (8 * sDlen) = vk ∧ word m' B (8 * sP) = vp ∧
    word m' B (8 * sPlen) = vpl ∧ word m' B (8 * sDP) = vp ∧ word m' B (8 * sQI) = vp ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sDQ) = vq ∧ word m' B (8 * sQlen) = vql ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold m' ppEntryMem ppEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `entry` leaves: `vg_rsa_check_key`'s header, with `pre` and its
length as `e`'s, `n` as `d`, `p` as `dP` and `qInv`, and `q` as `dQ`. -/
structure PpEntryPost (s : State) (B : Addr) (t : State) : Prop where
  rdi : t.gpr .rdi = B
  saved : ∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)
  hN : word t.mem B (8 * sN) = s.gpr .rdx
  hK : word t.mem B (8 * sK) = s.gpr .rcx
  hE : word t.mem B (8 * sE) = s.gpr .rdi
  hEl : word t.mem B (8 * sElen) = s.gpr .rsi
  hD : word t.mem B (8 * sD) = s.gpr .rdx
  hDl : word t.mem B (8 * sDlen) = s.gpr .rcx
  hP : word t.mem B (8 * sP) = s.gpr .r8
  hPl : word t.mem B (8 * sPlen) = s.gpr .r9
  hDP : word t.mem B (8 * sDP) = s.gpr .r8
  hQI : word t.mem B (8 * sQI) = s.gpr .r8
  hQ : word t.mem B (8 * sQ) = stackArg s 0
  hDQ : word t.mem B (8 * sDQ) = stackArg s 0
  hQl : word t.mem B (8 * sQlen) = stackArg s 1
  out : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi] s t

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 2) in `rdi`. -/
theorem ppEntry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 4, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block Impl.Rsa.X86_64.PrivPre.entry) s (PpEntryPost s B) := by
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = B := hB
  have ha2 := ha 2 (by decide)
  rw [ppEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = ppEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e2, ha2, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sN (by decide),
      hw sK (by decide), hw sE (by decide), hw sElen (by decide), hw sD (by decide), hw sDlen (by decide),
      hw sP (by decide), hw sPlen (by decide), hw sDP (by decide), hw sQI (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact ppEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by
    xrun [h11₂]) rfl) fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = ppEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
      (stackArg s 1) := by
    rw [hm, hm₂, hm₁]; rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hN, hK, hE, hEl, hD, hDl, hP, hPl, hDP, hQI, hQ, hDQ, hQl, ho⟩ :=
    ppEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
      (stackArg s 1)
  rw [← hmem] at h0 h1 h2 h3 h4 h5 hN hK hE hEl hD hDl hP hPl hDP hQI hQ hDQ hQl ho
  refine ⟨hdi, fun i hi => ?_, hN, hK, hE, hEl, hD, hDl, hP, hPl, hDP, hQI, hQ, hDQ, hQl, ho,
    (k12.trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Rsa.X86_64.Key
